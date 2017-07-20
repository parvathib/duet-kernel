/*
 *  Copyright (C) 2008 Red Hat, Inc., Eric Paris <eparis@redhat.com>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2, or (at your option)
 *  any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; see the file COPYING.  If not, write to
 *  the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*
 * fsnotify inode mark locking/lifetime/and refcnting
 *
 * REFCNT:
 * The group->recnt and mark->refcnt tell how many "things" in the kernel
 * currently are referencing the objects. Both kind of objects typically will
 * live inside the kernel with a refcnt of 2, one for its creation and one for
 * the reference a group and a mark hold to each other.
 * If you are holding the appropriate locks, you can take a reference and the
 * object itself is guaranteed to survive until the reference is dropped.
 *
 * LOCKING:
 * There are 3 locks involved with fsnotify inode marks and they MUST be taken
 * in order as follows:
 *
 * group->mark_mutex
 * mark->lock
 * mark->connector->lock
 *
 * group->mark_mutex protects the marks_list anchored inside a given group and
 * each mark is hooked via the g_list.  It also protects the groups private
 * data (i.e group limits).

 * mark->lock protects the marks attributes like its masks and flags.
 * Furthermore it protects the access to a reference of the group that the mark
 * is assigned to as well as the access to a reference of the inode/vfsmount
 * that is being watched by the mark.
 *
 * mark->connector->lock protects the list of marks anchored inside an
 * inode / vfsmount and each mark is hooked via the i_list.
 *
 * A list of notification marks relating to inode / mnt is contained in
 * fsnotify_mark_connector. That structure is alive as long as there are any
 * marks in the list and is also protected by fsnotify_mark_srcu. A mark gets
 * detached from fsnotify_mark_connector when last reference to the mark is
 * dropped.  Thus having mark reference is enough to protect mark->connector
 * pointer and to make sure fsnotify_mark_connector cannot disappear. Also
 * because we remove mark from g_list before dropping mark reference associated
 * with that, any mark found through g_list is guaranteed to have
 * mark->connector set until we drop group->mark_mutex.
 *
 * LIFETIME:
 * Inode marks survive between when they are added to an inode and when their
 * refcnt==0. Marks are also protected by fsnotify_mark_srcu.
 *
 * The inode mark can be cleared for a number of different reasons including:
 * - The inode is unlinked for the last time.  (fsnotify_inode_remove)
 * - The inode is being evicted from cache. (fsnotify_inode_delete)
 * - The fs the inode is on is unmounted.  (fsnotify_inode_delete/fsnotify_unmount_inodes)
 * - Something explicitly requests that it be removed.  (fsnotify_destroy_mark)
 * - The fsnotify_group associated with the mark is going away and all such marks
 *   need to be cleaned up. (fsnotify_clear_marks_by_group)
 *
 * This has the very interesting property of being able to run concurrently with
 * any (or all) other directions.
 */

#include <linux/fs.h>
#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/kthread.h>
#include <linux/module.h>
#include <linux/mutex.h>
#include <linux/slab.h>
#include <linux/spinlock.h>
#include <linux/srcu.h>

#include <linux/atomic.h>

#include <linux/fsnotify_backend.h>
#include "fsnotify.h"

#define FSNOTIFY_REAPER_DELAY	(1)	/* 1 jiffy */

struct srcu_struct fsnotify_mark_srcu;
struct kmem_cache *fsnotify_mark_connector_cachep;

static DEFINE_SPINLOCK(destroy_lock);
static LIST_HEAD(destroy_list);
static struct fsnotify_mark_connector *connector_destroy_list;

static void fsnotify_mark_destroy_workfn(struct work_struct *work);
static DECLARE_DELAYED_WORK(reaper_work, fsnotify_mark_destroy_workfn);

static void fsnotify_connector_destroy_workfn(struct work_struct *work);
static DECLARE_WORK(connector_reaper_work, fsnotify_connector_destroy_workfn);

struct pool_mask{
	struct fsnotify_group *group;
	u32 mask;
	u32 updated;
	u32 private_id;
	struct hlist_node hentry;
};
atomic_t g_rutime;
#define FSNOTIFY_GROUP_MASK_BUCKETS 7
DEFINE_HASHTABLE(pooled_group_masks, FSNOTIFY_GROUP_MASK_BUCKETS); //maximum of 128 groups allowed

void fsnotify_get_mark(struct fsnotify_mark *mark)
{
	WARN_ON_ONCE(!atomic_read(&mark->refcnt));
	atomic_inc(&mark->refcnt);
}

/*
 * Get mark reference when we found the mark via lockless traversal of object
 * list. Mark can be already removed from the list by now and on its way to be
 * destroyed once SRCU period ends.
 */
static bool fsnotify_get_mark_safe(struct fsnotify_mark *mark)
{
	return atomic_inc_not_zero(&mark->refcnt);
}

static void __fsnotify_recalc_mask(struct fsnotify_mark_connector *conn)
{
	u32 new_mask = 0;
	struct fsnotify_mark *mark;

	assert_spin_locked(&conn->lock);
	hlist_for_each_entry(mark, &conn->list, obj_list) {
		if (mark->flags & FSNOTIFY_MARK_FLAG_ATTACHED)
			new_mask |= mark->mask;
	}
	if (conn->flags & FSNOTIFY_OBJ_TYPE_INODE)
		conn->inode->i_fsnotify_mask = new_mask;
	else if (conn->flags & FSNOTIFY_OBJ_TYPE_VFSMOUNT)
		real_mount(conn->mnt)->mnt_fsnotify_mask = new_mask;
}

/*
 * Calculate mask of events for a list of marks. The caller must make sure
 * connector and connector->inode cannot disappear under us.  Callers achieve
 * this by holding a mark->lock or mark->group->mark_mutex for a mark on this
 * list.
 */
void fsnotify_recalc_mask(struct fsnotify_mark_connector *conn)
{
	if (!conn)
		return;

	spin_lock(&conn->lock);
	__fsnotify_recalc_mask(conn);
	spin_unlock(&conn->lock);
	if (conn->flags & FSNOTIFY_OBJ_TYPE_INODE)
		__fsnotify_update_child_dentry_flags(conn->inode);
}

void fsnotify_update_existing_mark(struct fsnotify_mark *mark, 
				struct inode *inode, 
				u32 mask, 
				int implicit_rec_watch,
				int add) 
{
	u32 old_mask, new_mask;
	int ret;
	int add_rule = 0;
	int save_spare_mask = 0;
	u32 spare_mask = 0;

	spin_lock(&mark->lock);
	old_mask = mark->mask;
	
	if(!implicit_rec_watch) { //explicit add request
		if((fsnotify_is_rule_mark(mark) && !(mask & FS_RECURSIVE_ADD)) || // Re & N : Don't allow.
			(fsnotify_is_normal_mark(mark) && (mask & FS_RECURSIVE_ADD))){  // N & Re : Don't allow.
			ret = -EINVAL;
			spin_unlock(&mark->lock);
			goto end;
		}
		if(fsnotify_is_recursive_mark(mark)){ // If it Ri & (Re or N), always add the mask. The mark becomes of type N or Re 
			add = 1; 
			save_spare_mask = 1;
			spare_mask = mask;
			if(mask & FS_RECURSIVE_ADD) //If it is Ri & Re, add the rule to the list
				add_rule = 1;
			else //if Ri & N, make it a normal node. 
				mark->mask &= ~(FS_RECURSIVE_ADD);
		}
	}
	if((mask & FS_RECURSIVE_ADD) && (implicit_rec_watch)) { // implicit add request (Ri)
		if(fsnotify_is_normal_mark(mark) || fsnotify_is_rule_mark(mark)) { // If the current mark is R or N : Save the mask in spare_mask.
			save_spare_mask = 1;
			spare_mask = old_mask;
			mask &= ~(FS_RECURSIVE_ADD);
		}
	}
	if(!implicit_rec_watch && (mask & FS_RECURSIVE_ADD)) {
		ret = fsnotify_update_recursive_mark_list(&inode->i_fsnotify_marks, mark, add_rule); //add/update rule 
		if(!ret) {
			spin_unlock(&mark->lock);
			goto end;
		}		
	}
	if(!mark->spare_mask)
		mark->spare_mask = spare_mask;

	if (add)
		mark->mask |= mask;
	else
		mark->mask = mask;

	new_mask = mark->mask;
	spin_unlock(&mark->lock);

	if (old_mask != new_mask) {
		/* more bits in old than in new? */
		int dropped = (old_mask & ~new_mask);
		/* more bits in this mark than the inode's mask? */
		int do_inode = (new_mask & ~inode->i_fsnotify_mask);

		/* update the inode with this new mark */
		if (dropped || do_inode)
			fsnotify_recalc_mask(inode->i_fsnotify_marks);

	}
	return;
}
/* Free all connectors queued for freeing once SRCU period ends */
static void fsnotify_connector_destroy_workfn(struct work_struct *work)
{
	struct fsnotify_mark_connector *conn, *free;

	spin_lock(&destroy_lock);
	conn = connector_destroy_list;
	connector_destroy_list = NULL;
	spin_unlock(&destroy_lock);

	synchronize_srcu(&fsnotify_mark_srcu);
	while (conn) {
		free = conn;
		conn = conn->destroy_next;
		kmem_cache_free(fsnotify_mark_connector_cachep, free);
	}
}

static struct inode *fsnotify_detach_connector_from_object(
					struct fsnotify_mark_connector *conn)
{
	struct inode *inode = NULL;

	if (conn->flags & FSNOTIFY_OBJ_TYPE_INODE) {
		inode = conn->inode;
		rcu_assign_pointer(inode->i_fsnotify_marks, NULL);
		inode->i_fsnotify_mask = 0;
		conn->inode = NULL;
		conn->flags &= ~FSNOTIFY_OBJ_TYPE_INODE;
	} else if (conn->flags & FSNOTIFY_OBJ_TYPE_VFSMOUNT) {
		rcu_assign_pointer(real_mount(conn->mnt)->mnt_fsnotify_marks,
				   NULL);
		real_mount(conn->mnt)->mnt_fsnotify_mask = 0;
		conn->mnt = NULL;
		conn->flags &= ~FSNOTIFY_OBJ_TYPE_VFSMOUNT;
	}

	return inode;
}

static void fsnotify_final_mark_destroy(struct fsnotify_mark *mark)
{
	struct fsnotify_group *group = mark->group;

	if (WARN_ON_ONCE(!group))
		return;
	group->ops->free_mark(mark);
	fsnotify_put_group(group);
}

void fsnotify_put_mark(struct fsnotify_mark *mark)
{
	struct fsnotify_mark_connector *conn;
	struct inode *inode = NULL;
	bool free_conn = false;

	/* Catch marks that were actually never attached to object */
	if (!mark->connector) {
		if (atomic_dec_and_test(&mark->refcnt))
			fsnotify_final_mark_destroy(mark);
		return;
	}

	/*
	 * We have to be careful so that traversals of obj_list under lock can
	 * safely grab mark reference.
	 */
	if (!atomic_dec_and_lock(&mark->refcnt, &mark->connector->lock))
		return;

	conn = mark->connector;
	hlist_del_init_rcu(&mark->obj_list);
	if (hlist_empty(&conn->list)) {
		inode = fsnotify_detach_connector_from_object(conn);
		free_conn = true;
	} else {
		__fsnotify_recalc_mask(conn);
	}
	mark->connector = NULL;
	spin_unlock(&conn->lock);

	iput(inode);

	if (free_conn) {
		spin_lock(&destroy_lock);
		conn->destroy_next = connector_destroy_list;
		connector_destroy_list = conn;
		spin_unlock(&destroy_lock);
		queue_work(system_unbound_wq, &connector_reaper_work);
	}
	/*
	 * Note that we didn't update flags telling whether inode cares about
	 * what's happening with children. We update these flags from
	 * __fsnotify_parent() lazily when next event happens on one of our
	 * children.
	 */
	spin_lock(&destroy_lock);
	list_add(&mark->g_list, &destroy_list);
	spin_unlock(&destroy_lock);
	queue_delayed_work(system_unbound_wq, &reaper_work,
			   FSNOTIFY_REAPER_DELAY);
}

bool fsnotify_prepare_user_wait(struct fsnotify_iter_info *iter_info)
{
	struct fsnotify_group *group;

	if (WARN_ON_ONCE(!iter_info->inode_mark && !iter_info->vfsmount_mark))
		return false;

	if (iter_info->inode_mark)
		group = iter_info->inode_mark->group;
	else
		group = iter_info->vfsmount_mark->group;

	/*
	 * Since acquisition of mark reference is an atomic op as well, we can
	 * be sure this inc is seen before any effect of refcount increment.
	 */
	atomic_inc(&group->user_waits);

	if (iter_info->inode_mark) {
		/* This can fail if mark is being removed */
		if (!fsnotify_get_mark_safe(iter_info->inode_mark))
			goto out_wait;
	}
	if (iter_info->vfsmount_mark) {
		if (!fsnotify_get_mark_safe(iter_info->vfsmount_mark))
			goto out_inode;
	}

	/*
	 * Now that both marks are pinned by refcount in the inode / vfsmount
	 * lists, we can drop SRCU lock, and safely resume the list iteration
	 * once userspace returns.
	 */
	srcu_read_unlock(&fsnotify_mark_srcu, iter_info->srcu_idx);

	return true;
out_inode:
	if (iter_info->inode_mark)
		fsnotify_put_mark(iter_info->inode_mark);
out_wait:
	if (atomic_dec_and_test(&group->user_waits) && group->shutdown)
		wake_up(&group->notification_waitq);
	return false;
}

void fsnotify_finish_user_wait(struct fsnotify_iter_info *iter_info)
{
	struct fsnotify_group *group = NULL;

	iter_info->srcu_idx = srcu_read_lock(&fsnotify_mark_srcu);
	if (iter_info->inode_mark) {
		group = iter_info->inode_mark->group;
		fsnotify_put_mark(iter_info->inode_mark);
	}
	if (iter_info->vfsmount_mark) {
		group = iter_info->vfsmount_mark->group;
		fsnotify_put_mark(iter_info->vfsmount_mark);
	}
	/*
	 * We abuse notification_waitq on group shutdown for waiting for all
	 * marks pinned when waiting for userspace.
	 */
	if (atomic_dec_and_test(&group->user_waits) && group->shutdown)
		wake_up(&group->notification_waitq);
}

/*
 * Mark mark as detached, remove it from group list. Mark still stays in object
 * list until its last reference is dropped. Note that we rely on mark being
 * removed from group list before corresponding reference to it is dropped. In
 * particular we rely on mark->connector being valid while we hold
 * group->mark_mutex if we found the mark through g_list.
 *
 * Must be called with group->mark_mutex held. The caller must either hold
 * reference to the mark or be protected by fsnotify_mark_srcu.
 */
void fsnotify_detach_mark(struct fsnotify_mark *mark)
{
	struct fsnotify_group *group = mark->group;

	WARN_ON_ONCE(!mutex_is_locked(&group->mark_mutex));
	WARN_ON_ONCE(!srcu_read_lock_held(&fsnotify_mark_srcu) &&
		     atomic_read(&mark->refcnt) < 1 +
			!!(mark->flags & FSNOTIFY_MARK_FLAG_ATTACHED));

	spin_lock(&mark->lock);
	/* something else already called this function on this mark */
	if (!(mark->flags & FSNOTIFY_MARK_FLAG_ATTACHED)) {
		spin_unlock(&mark->lock);
		return;
	}
	mark->flags &= ~FSNOTIFY_MARK_FLAG_ATTACHED;
	list_del_init(&mark->g_list);
	spin_unlock(&mark->lock);

	atomic_dec(&group->num_marks);

	/* Drop mark reference acquired in fsnotify_add_mark_locked() */
	fsnotify_put_mark(mark);
}

/*
 * Free fsnotify mark. The mark is actually only marked as being freed.  The
 * freeing is actually happening only once last reference to the mark is
 * dropped from a workqueue which first waits for srcu period end.
 *
 * Caller must have a reference to the mark or be protected by
 * fsnotify_mark_srcu.
 */
void fsnotify_free_mark(struct fsnotify_mark *mark)
{
	struct fsnotify_group *group = mark->group;

	spin_lock(&mark->lock);
	/* something else already called this function on this mark */
	if (!(mark->flags & FSNOTIFY_MARK_FLAG_ALIVE)) {
		spin_unlock(&mark->lock);
		return;
	}
	mark->flags &= ~FSNOTIFY_MARK_FLAG_ALIVE;
	spin_unlock(&mark->lock);

	/*
	 * Some groups like to know that marks are being freed.  This is a
	 * callback to the group function to let it know that this mark
	 * is being freed.
	 */
	if (group->ops->freeing_mark)
		group->ops->freeing_mark(mark, group);
}

void fsnotify_destroy_mark(struct fsnotify_mark *mark,
			   struct fsnotify_group *group)
{
	mutex_lock_nested(&group->mark_mutex, SINGLE_DEPTH_NESTING);
	fsnotify_detach_mark(mark);
	mutex_unlock(&group->mark_mutex);
	fsnotify_free_mark(mark);
}

/*
 * Sorting function for lists of fsnotify marks.
 *
 * Fanotify supports different notification classes (reflected as priority of
 * notification group). Events shall be passed to notification groups in
 * decreasing priority order. To achieve this marks in notification lists for
 * inodes and vfsmounts are sorted so that priorities of corresponding groups
 * are descending.
 *
 * Furthermore correct handling of the ignore mask requires processing inode
 * and vfsmount marks of each group together. Using the group address as
 * further sort criterion provides a unique sorting order and thus we can
 * merge inode and vfsmount lists of marks in linear time and find groups
 * present in both lists.
 *
 * A return value of 1 signifies that b has priority over a.
 * A return value of 0 signifies that the two marks have to be handled together.
 * A return value of -1 signifies that a has priority over b.
 */
int fsnotify_compare_groups(struct fsnotify_group *a, struct fsnotify_group *b)
{
	if (a == b)
		return 0;
	if (!a)
		return 1;
	if (!b)
		return -1;
	if (a->priority < b->priority)
		return 1;
	if (a->priority > b->priority)
		return -1;
	if (a < b)
		return 1;
	return -1;
}

static int fsnotify_attach_connector_to_object(
				struct fsnotify_mark_connector __rcu **connp,
				struct inode *inode,
				struct vfsmount *mnt)
{
	struct fsnotify_mark_connector *conn;

	conn = kmem_cache_alloc(fsnotify_mark_connector_cachep, GFP_KERNEL);
	if (!conn)
		return -ENOMEM;
	spin_lock_init(&conn->lock);
	INIT_HLIST_HEAD(&conn->list);
	atomic_set(&conn->nrules, 0); 
	atomic_set(&conn->r_utime, 0);
	INIT_HLIST_HEAD(&conn->r_list); 
	if (inode) {
		conn->flags = FSNOTIFY_OBJ_TYPE_INODE;
		conn->inode = igrab(inode);
	} else {
		conn->flags = FSNOTIFY_OBJ_TYPE_VFSMOUNT;
		conn->mnt = mnt;
	}
	/*
	 * cmpxchg() provides the barrier so that readers of *connp can see
	 * only initialized structure
	 */
	if (cmpxchg(connp, NULL, conn)) {
		/* Someone else created list structure for us */
		if (inode)
			iput(inode);
		kmem_cache_free(fsnotify_mark_connector_cachep, conn);
	}

	return 0;
}

/*
 * Get mark connector, make sure it is alive and return with its lock held.
 * This is for users that get connector pointer from inode or mount. Users that
 * hold reference to a mark on the list may directly lock connector->lock as
 * they are sure list cannot go away under them.
 */
static struct fsnotify_mark_connector *fsnotify_grab_connector(
				struct fsnotify_mark_connector __rcu **connp)
{
	struct fsnotify_mark_connector *conn;
	int idx;

	idx = srcu_read_lock(&fsnotify_mark_srcu);
	conn = srcu_dereference(*connp, &fsnotify_mark_srcu);
	if (!conn)
		goto out;
	spin_lock(&conn->lock);
	if (!(conn->flags & (FSNOTIFY_OBJ_TYPE_INODE |
			     FSNOTIFY_OBJ_TYPE_VFSMOUNT))) {
		spin_unlock(&conn->lock);
		srcu_read_unlock(&fsnotify_mark_srcu, idx);
		return NULL;
	}
out:
	srcu_read_unlock(&fsnotify_mark_srcu, idx);
	return conn;
}

/* 
 * add a mark in recursive rule. Set the bit FSNOTIFY_OBJ_TYPE_REC_RULE in connector flags. 
 * This is useful when we calculate the cumilative mask when we implicitly add a mark which
 * falls in the subtree under this rule. 
 */
static void __fsnotify_update_recursive_mark_list(struct fsnotify_mark_connector *conn,
				struct fsnotify_mark *mark, int add) 
{
	int rutime;
	if(add) {
		hlist_add_head_rcu(&mark->rule_list, &conn->r_list);
		conn->flags |= FSNOTIFY_OBJ_TYPE_REC_RULE;
		mark->flags |= FSNOTIFY_MARK_FLAG_RULE;
		atomic_set(&conn->r_utime, 0); //TODO : Can use lazy add rule
	}
	atomic_inc(&g_rutime);
}

int fsnotify_update_recursive_mark_list(struct fsnotify_mark_connector __rcu **connp,
				struct fsnotify_mark *mark,
				int add)
{
	struct fsnotify_mark_connector *conn;
	conn = fsnotify_grab_connector(connp);
	if(!conn) {
		return -EFAULT;
	}
	__fsnotify_update_recursive_mark_list(conn, mark, add);
	spin_unlock(&conn->lock);
	return 0;
}

int fsnotify_destroy_recursive_mark(struct fsnotify_mark *mark,
				    struct fsnotify_group *group)
{
	struct fsnotify_mark_connector *conn;
	int ret = 0;
	conn = mark->connector;
	if(!conn) {
		return -EINVAL;
	}
	mutex_lock_nested(&group->mark_mutex, SINGLE_DEPTH_NESTING);
	spin_lock(&mark->lock);
	if(!mark->spare_mask) {
		ret = -ENOENT;
		goto out;
	}
		mark->mask = mark->spare_mask;
		mark->spare_mask = 0;
		__fsnotify_recalc_mask(conn);
		if(mark->flags & FSNOTIFY_MARK_FLAG_RULE)
			mark->flags &= ~(FSNOTIFY_MARK_FLAG_RULE);
		if(hlist_empty(&conn->r_list)) {
			spin_lock(&conn->lock);
			conn->flags &= ~(FSNOTIFY_OBJ_TYPE_REC_RULE);
			spin_unlock(&conn->lock);
		}	
	}
out:
	spin_unlock(&mark->lock);
	mutex_unlock(&group->mark_mutex);
	return ret;
}

struct pool_mask *fsnotify_find_hnode(struct fsnotify_group *group) 
{
	struct pool_mask *pmask_node;
	hash_for_each_possible(pooled_group_masks, pmask_node, hentry, (unsigned long)group)
	return pmask_node;
}

int fsnotify_add_hnode(struct pool_mask *hnode, struct fsnotify_group *group)
{
	int alloc_len = sizeof(struct pool_mask);
	hnode = kmalloc(alloc_len, GFP_KERNEL);
	if(unlikely(!hnode)) {
		return -ENOMEM; 	
	}
	hnode->group = group;
	hash_add(pooled_group_masks, &hnode->hentry, (unsigned long)group);
	return 0;	
}

int fsnotify_init_hnode(struct pool_mask *hnode, struct fsnotify_group *group)
{
	int alloc_len = sizeof(struct pool_mask);
	memset(hnode, 0,, alloc_len);
	hnode->group = group;
	return 0;	
}
void fsnotify_free_pooled_masks(void)
{
	int bkt;
	struct pool_mask *pmask_node;
	hash_for_each(pooled_group_masks, bkt, pmask_node, hentry) {
		hash_del(&pmask_node->hentry);
		kfree(pmask_node);
	} 
}
void fsnotify_update_inode_rule_time(struct fsnotify_mark_connector __rcu **connp) {
	int global_rutime = atomic_read(g_rutime);
	struct fsnotify_mark_connector *conn = fsnotify_grab_connector(connp);
	atomic_set(&conn->r_utime, global_rutime);
	spin_unlock(&conn->lock);
	return;	
}
int __fsnotify_update_marks_inode(struct inode *inode) 
{
	struct fsnotify_mark_connector *inode_conn;	
	struct hlist_node *inode_node = NULL, *vfsmount_node = NULL, *rule_node = NULL;
	struct fsnotify_mark *inode_mark = NULL, *vfsmount_mark = NULL;
	struct fsnotify_group *inode_group, *vfsmount_group;
	struct fsnotify_iter_info iter_info;
	struct pool_mask *hash_node;
	int ret = 0;
	u32 new_mask = 0;
	u32 orig_mask = 0;
	iter_info.srcu_idx = srcu_read_lock(&fsnotify_mark_srcu);
	
	inode_conn = srcu_dereference(inode->i_fsnotify_marks, &fsnotify_mark_srcu);
	if(!inode_conn) { 
		ret =  -EINVAL;
		goto out;
	}
	/* Get the reference of head of rules list for this inode */	
	rule_node = srcu_dereference(inode_conn->r_list.first,
						&fsnotify_mark_srcu);
	while(rule_node) { /* Only rules node will execute this code */
		inode_group = NULL; 
		inode_mark = NULL;
		/* Iterate over the rule list and caculate */
		inode_mark = hlist_entry(srcu_dereference(rule_node, &fsnotify_mark_srcu),
					 struct fsnotify_mark, rule_list);
		inode_group = inode_mark->group;
		/*
		 * 1. for each rule, check if the hash node exists to be updated or create it
		 * 2. update the hash node: get the new updated mask (old mask | orig_mask). 
		 *    call the updating mark function. Mark the hash node is updated on the hash node and 
		 * 3. If hash table is not empty, check if the rest of the marks need to be updated or not.
		 *    for each mark in the marks list, if there is an entry in the hash table which is not updated,
		 *    call update mark. 
		 * 4. Go through the hash list and check if there are any hash nodes which are yet to be updated. 
		 *    As you leave the hash nodes, reset the bit.
		 */ 
		if(inode_group && (inode_mark->flags & FSNOTIFY_MARK_FLAG_RULE)) {
			hash_node = fsnotify_find_hnode(inode_group);
			if(!hash_node) {
				ret = fsnotify_add_hnode(hash_node, inode_group);
				if(ret)
					goto out;
			}
			orig_mask =  inode_mark->spare_mask;			
			new_mask = hash_node->mask | orig_mask;
			fsnotify_update_existing_mark(inode_mark, inode, new_mask, 0); 
			hash_node->mask = inode_mark->mark;
			
			
		}
		rule_node = srcu_dereference(rule_node->next,
						      &fsnotify_mark_srcu);	
	}

	
	/* start adding/updating the marks at this node */
	if(hash_empty(pooled_group_masks))
		goto out;
	inode_node = srcu_dereference(inode_conn->list.first,
					      &fsnotify_mark_srcu);
	while(inode_node) {
			
	}
	
out:
	srcu_read_unlock(&fsnotify_mark_srcu, iter_info.srcu_idx);
	return ret;
}

int  fsnotify_is_latest(struct inode *inode) 
{
	int ret = 0;
	int idx;
	if (inode)
		connp = &inode->i_fsnotify_marks;
	else
		connp = &real_mount(mnt)->mnt_fsnotify_marks;
	/* dereference this inode connector */
	idx = srcu_read_lock(&fsnotify_mark_srcu);
	conn = srcu_dereference(*connp, &fsnotify_mark_srcu);
	if (atomic_read(&conn->r_utime) == atomic_read(&g_rutime)) {
		ret = 1;
	}
	srcu_read_unlock(&fsnotify_mark_srcu, idx);
	return ret;
}

int fsnotify_update_marks_inodes(struct dentry *dentry, struct inode *inode)
{
	struct dentry *parent;
	dget(dentry);
	if(IS_ROOT(dentry) || fsnotify_is_latest(inode)) {
		ret =  __fsnotify_update_marks_inode(inode);
		goto out;
	}
	parent = dget_parent(dentry);
	ret = fsnotify_update_marks_inodes(parent, d_inode(parent));
	if(!ret)
		ret = __fsnotify_update_marks_inode(inode);
out:	
	dput(dentry);
	return ret;
}

struct dentry *fsnotify_get_dentry(struct inode* inode,
                                const unsigned char *file_name)
{      
	spin_lock(&inode->i_lock); 
        if(hlist_empty(&inode->i_dentry)) {
                return NULL;
        }
        hlist_for_each_entry(alias, &inode->i_dentry, d_u.d_alias) {
                if (IS_ROOT(alias) && (alias->d_flags & DCACHE_DISCONNECTED))
                        continue;
                if(!strcmp(alias->d_name.name, file_name)){
                        break;
                }
        }
	spin_unlock(&inode->i_lock);
        //dget(alias);
	return alias;
}
#if 0
int fsnotify_calculate_recursive_masks(struct inode *inode, struct mount *mnt, struct dentry *dentry) 
{
	struct dentry *parent, *old_parent = NULL;
	struct inode *p_inode;
	struct fsnotify_mark_connector *conn;
	int ret = -EINVAL;
	int inode_rule_utime;
	int global_rule_utime;
	/*initialize hash table */
	hash_init(pooled_group_masks);

	
#if 0
	if(IS_ROOT(dentry)) { //If this is the root directory, no need to pool the masks
		fsnotify_update_inode_rule_time(&inode->i_fsnotify_marks);
		ret = 0;
		goto out;
	}
	parent = dentry;
	while(1) {

		if(IS_ROOT(parent) || !(ret)) { //Once you reach root, stop climbing up:
			ret = fsnotify_calculate_mask(inode);
			srcu_read_unlock(&fsnotify_mark_srcu, idx);
			break;
		}
		parent = dget_parent(parent);
		dput(old_parent);
		old_parent = parent;
		inode = d_inode(parent);
		idx = srcu_read_lock(&fsnotify_mark_srcu);
		conn = srcu_dereference(inode->i_fsnotify_marks, &fsnotify_mark_srcu);
		if(!conn) {
			continue;
		}
		if(atomic_read(&conn->r_utime) == atomic_read(&g_rutime)) {	 
			 /* calculate the recursive masks from the latest inode and break */ 
			ret = 0;  
			continue;
		}
		/* Push the inode address in a stack if its a rule */
	}
	dput(old_parent);
	/* 
	 * We should get the latest rule/ root's masks here
	 * Pop the inodes of the rules and update masks for existing marks and create new ones on the way back
	 * at the end we pop the nearest rule and update it's masks too.
	 * return the latest mask
	 */
#endif 
out:	
	dput(dentry);
	return ret;
}

#endif
int fsnotify_apply_recursive_rules(struct inode *inode, struct mount *mnt, 
				const unsigned char *file_name)
{
	int ret = 0;
	struct fsnotify_mark_connector __rcu **connp;
	struct fsnotify_mark_connector *conn;
	struct dentry *i_dentry = NULL;
	/* If the global and inode rule update time stamps match, return */
	if(fsnotify_is_latest(inode)) {
		return ret;	
	}
	if(!file_name) {
		i_dentry = fsnotify_get_dentry(inode, file_name);
	}
	else {
		i_dentry = d_find_alias(inode);
	}
	ret = fsnotify_update_marks_inodes(i_dentry, inode); //TODO: should add support for vfsmount
	return ret;		
}



/*
 * Add mark into proper place in given list of marks. These marks may be used
 * for the fsnotify backend to determine which event types should be delivered
 * to which group and for which inodes. These marks are ordered according to
 * priority, highest number first, and then by the group's location in memory.
 */
static int fsnotify_add_mark_list(struct fsnotify_mark *mark,
				  struct inode *inode, struct vfsmount *mnt,
				  int allow_dups, int implicit_rec_add)
{
	struct fsnotify_mark *lmark, *last = NULL;
	struct fsnotify_mark_connector *conn;
	struct fsnotify_mark_connector __rcu **connp;
	int cmp;
	int err = 0;

	if (WARN_ON(!inode && !mnt))
		return -EINVAL;
	if (inode)
		connp = &inode->i_fsnotify_marks;
	else
		connp = &real_mount(mnt)->mnt_fsnotify_marks;
restart:
	spin_lock(&mark->lock);
	conn = fsnotify_grab_connector(connp);
	if (!conn) {
		spin_unlock(&mark->lock);
		err = fsnotify_attach_connector_to_object(connp, inode, mnt);
		if (err)
			return err;
		goto restart;
	}
	/* add mark to the rule list if user explicitly requests with the flag */
	if(!implicit_rec_add && (mark->mask & FS_RECURSIVE_ADD)) {
		__fsnotify_update_recursive_mark_list(conn, mark, 1);
	}
	/* is mark the first mark? */
	if (hlist_empty(&conn->list)) {
		hlist_add_head_rcu(&mark->obj_list, &conn->list);
		goto added;
	}

	/* should mark be in the middle of the current list? */
	hlist_for_each_entry(lmark, &conn->list, obj_list) {
		last = lmark;

		if ((lmark->group == mark->group) &&
		    (lmark->flags & FSNOTIFY_MARK_FLAG_ATTACHED) &&
		    !allow_dups) {
			err = -EEXIST;
			goto out_err;
		}

		cmp = fsnotify_compare_groups(lmark->group, mark->group);
		if (cmp >= 0) {
			hlist_add_before_rcu(&mark->obj_list, &lmark->obj_list);
			goto added;
		}
	}

	BUG_ON(last == NULL);
	/* mark should be the last entry.  last is the current last entry */
	hlist_add_behind_rcu(&mark->obj_list, &last->obj_list);
added:
	mark->connector = conn;
out_err:
	spin_unlock(&conn->lock);
	spin_unlock(&mark->lock);
	return err;
}

/*
 * Attach an initialized mark to a given group and fs object.
 * These marks may be used for the fsnotify backend to determine which
 * event types should be delivered to which group.
 */
int fsnotify_add_mark_locked(struct fsnotify_mark *mark, struct inode *inode,
			     struct vfsmount *mnt, int allow_dups, int implicit_rec_add)
{
	struct fsnotify_group *group = mark->group;
	int ret = 0;

	BUG_ON(inode && mnt);
	BUG_ON(!inode && !mnt);
	BUG_ON(!mutex_is_locked(&group->mark_mutex));

	/*
	 * LOCKING ORDER!!!!
	 * group->mark_mutex
	 * mark->lock
	 * mark->connector->lock
	 */
	spin_lock(&mark->lock);
	mark->flags |= FSNOTIFY_MARK_FLAG_ALIVE | FSNOTIFY_MARK_FLAG_ATTACHED;

	list_add(&mark->g_list, &group->marks_list);
	atomic_inc(&group->num_marks);
	fsnotify_get_mark(mark); /* for g_list */
	spin_unlock(&mark->lock);
	ret = fsnotify_add_mark_list(mark, inode, mnt, allow_dups, implicit_rec_add);
	if (ret)
		goto err;

	if (mark->mask)
		fsnotify_recalc_mask(mark->connector);

	return ret;
err:
	mark->flags &= ~(FSNOTIFY_MARK_FLAG_ALIVE |
			 FSNOTIFY_MARK_FLAG_ATTACHED);
	if(mark->flags & FSNOTIFY_MARK_FLAG_RULE)
		mark->flags &= ~(FSNOTIFY_MARK_FLAG_RULE);
	list_del_init(&mark->g_list);
	atomic_dec(&group->num_marks);

	fsnotify_put_mark(mark);
	return ret;
}

int fsnotify_add_mark(struct fsnotify_mark *mark, struct inode *inode,
		      struct vfsmount *mnt, int allow_dups)
{
	int ret;
	struct fsnotify_group *group = mark->group;

	mutex_lock(&group->mark_mutex);
	ret = fsnotify_add_mark_locked(mark, inode, mnt, allow_dups, 0); //Note: for now, adding it here. May need to change the caller too
	mutex_unlock(&group->mark_mutex);
	return ret;
}

/*
 * Given a list of marks, find the mark associated with given group. If found
 * take a reference to that mark and return it, else return NULL.
 */
struct fsnotify_mark *fsnotify_find_mark(
				struct fsnotify_mark_connector __rcu **connp,
				struct fsnotify_group *group)
{
	struct fsnotify_mark_connector *conn;
	struct fsnotify_mark *mark;

	conn = fsnotify_grab_connector(connp);
	if (!conn)
		return NULL;

	hlist_for_each_entry(mark, &conn->list, obj_list) {
		if (mark->group == group &&
		    (mark->flags & FSNOTIFY_MARK_FLAG_ATTACHED)) {
			fsnotify_get_mark(mark);
			spin_unlock(&conn->lock);
			return mark;
		}
	}
	spin_unlock(&conn->lock);
	return NULL;
}

/* Clear any marks in a group with given type */
void fsnotify_clear_marks_by_group(struct fsnotify_group *group,
				   unsigned int type)
{
	struct fsnotify_mark *lmark, *mark;
	LIST_HEAD(to_free);
	struct list_head *head = &to_free;

	/* Skip selection step if we want to clear all marks. */
	if (type == FSNOTIFY_OBJ_ALL_TYPES) {
		head = &group->marks_list;
		goto clear;
	}
	/*
	 * We have to be really careful here. Anytime we drop mark_mutex, e.g.
	 * fsnotify_clear_marks_by_inode() can come and free marks. Even in our
	 * to_free list so we have to use mark_mutex even when accessing that
	 * list. And freeing mark requires us to drop mark_mutex. So we can
	 * reliably free only the first mark in the list. That's why we first
	 * move marks to free to to_free list in one go and then free marks in
	 * to_free list one by one.
	 */
	mutex_lock_nested(&group->mark_mutex, SINGLE_DEPTH_NESTING);
	list_for_each_entry_safe(mark, lmark, &group->marks_list, g_list) {
		if (mark->connector->flags & type)
			list_move(&mark->g_list, &to_free);
	}
	mutex_unlock(&group->mark_mutex);

clear:
	while (1) {
		mutex_lock_nested(&group->mark_mutex, SINGLE_DEPTH_NESTING);
		if (list_empty(head)) {
			mutex_unlock(&group->mark_mutex);
			break;
		}
		mark = list_first_entry(head, struct fsnotify_mark, g_list);
		fsnotify_get_mark(mark);
		fsnotify_detach_mark(mark);
		mutex_unlock(&group->mark_mutex);
		fsnotify_free_mark(mark);
		fsnotify_put_mark(mark);
	}
}

/* Destroy all marks attached to inode / vfsmount */
void fsnotify_destroy_marks(struct fsnotify_mark_connector __rcu **connp)
{
	struct fsnotify_mark_connector *conn;
	struct fsnotify_mark *mark, *old_mark = NULL;
	struct inode *inode;

	conn = fsnotify_grab_connector(connp);
	if (!conn)
		return;
	/*
	 * We have to be careful since we can race with e.g.
	 * fsnotify_clear_marks_by_group() and once we drop the conn->lock, the
	 * list can get modified. However we are holding mark reference and
	 * thus our mark cannot be removed from obj_list so we can continue
	 * iteration after regaining conn->lock.
	 */
	hlist_for_each_entry(mark, &conn->list, obj_list) {
		fsnotify_get_mark(mark);
		spin_unlock(&conn->lock);
		if (old_mark)
			fsnotify_put_mark(old_mark);
		old_mark = mark;
		fsnotify_destroy_mark(mark, mark->group);
		spin_lock(&conn->lock);
	}
	/*
	 * Detach list from object now so that we don't pin inode until all
	 * mark references get dropped. It would lead to strange results such
	 * as delaying inode deletion or blocking unmount.
	 */
	inode = fsnotify_detach_connector_from_object(conn);
	spin_unlock(&conn->lock);
	if (old_mark)
		fsnotify_put_mark(old_mark);
	iput(inode);
}

/*
 * Nothing fancy, just initialize lists and locks and counters.
 */
void fsnotify_init_mark(struct fsnotify_mark *mark,
			struct fsnotify_group *group)
{
	memset(mark, 0, sizeof(*mark));
	spin_lock_init(&mark->lock);
	atomic_set(&mark->refcnt, 1);
	fsnotify_get_group(group);
	mark->group = group;
	mark->spare_mask = 0;	
}

/*
 * Destroy all marks in destroy_list, waits for SRCU period to finish before
 * actually freeing marks.
 */
static void fsnotify_mark_destroy_workfn(struct work_struct *work)
{
	struct fsnotify_mark *mark, *next;
	struct list_head private_destroy_list;

	spin_lock(&destroy_lock);
	/* exchange the list head */
	list_replace_init(&destroy_list, &private_destroy_list);
	spin_unlock(&destroy_lock);

	synchronize_srcu(&fsnotify_mark_srcu);

	list_for_each_entry_safe(mark, next, &private_destroy_list, g_list) {
		list_del_init(&mark->g_list);
		fsnotify_final_mark_destroy(mark);
	}
}

/* Wait for all marks queued for destruction to be actually destroyed */
void fsnotify_wait_marks_destroyed(void)
{
	flush_delayed_work(&reaper_work);
}
