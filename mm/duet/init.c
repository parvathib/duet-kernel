/*
 * Copyright (C) 2016 George Amvrosiadis.  All rights reserved.
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License v2 as published by the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 */

#include "common.h"
#include "syscall.h"

struct duet_info duet_env;
duet_hook_t *duet_hook_fp;
EXPORT_SYMBOL(duet_hook_fp);

int duet_online(void)
{
	return (atomic_read(&duet_env.status) == DUET_STATUS_ON);
}

int duet_bootstrap(__u16 numtasks)
{
	if (atomic_cmpxchg(&duet_env.status, DUET_STATUS_OFF, DUET_STATUS_INIT)
	    != DUET_STATUS_OFF) {
		pr_err("duet: framework on, bootstrap aborted\n");
		return 1;
	}

	duet_env.numtasks = (numtasks ? numtasks : DUET_DEF_NUMTASKS);

	/* Initialize global hash table */
	if (hash_init()) {
		pr_err("duet: failed to initialize hash table\n");
		return 1;
	}

	/* Initialize task list */
	INIT_LIST_HEAD(&duet_env.tasks);
	mutex_init(&duet_env.task_list_mutex);
	atomic_set(&duet_env.status, DUET_STATUS_ON);

	rcu_assign_pointer(duet_hook_fp, duet_hook);
	synchronize_rcu();
	return 0;
}

int duet_shutdown(void)
{
	struct duet_task *task;

	if (atomic_cmpxchg(&duet_env.status, DUET_STATUS_ON, DUET_STATUS_CLEAN)
	    != DUET_STATUS_ON) {
		pr_err("duet: framework off, shutdown aborted\n");
		return 1;
	}

	rcu_assign_pointer(duet_hook_fp, NULL);
	synchronize_rcu();

	/* Remove all tasks */
	mutex_lock(&duet_env.task_list_mutex);
	while (!list_empty(&duet_env.tasks)) {
		task = list_entry_rcu(duet_env.tasks.next, struct duet_task,
				task_list);
		list_del_rcu(&task->task_list);
		mutex_unlock(&duet_env.task_list_mutex);

		/* Make sure everyone's let go before we free it */
		synchronize_rcu();
		wait_event(task->cleaner_queue,
			atomic_read(&task->refcount) == 0);
		duet_task_dispose(task);

		mutex_lock(&duet_env.task_list_mutex);
	}
	mutex_unlock(&duet_env.task_list_mutex);

	/* Destroy global hash table */
	vfree((void *)duet_env.itm_hash_table);

	INIT_LIST_HEAD(&duet_env.tasks);
	mutex_destroy(&duet_env.task_list_mutex);
	atomic_set(&duet_env.status, DUET_STATUS_OFF);
	return 0;
}

SYSCALL_DEFINE2(duet_status, u16, flags, struct duet_status_args __user *, arg)
{
	int ret = 0;
	struct duet_status_args *sa;

	if (!capable(CAP_SYS_ADMIN))
		return -EPERM;

	sa = memdup_user(arg, sizeof(*sa));
	if (IS_ERR(sa))
		return PTR_ERR(sa);

	/* For now, we only support one struct size */
	if (sa->size != sizeof(*sa)) {
		pr_err("duet_status: invalid args struct size (%u)\n",
			sa->size);
		ret = -EINVAL;
		goto done;
	}

	/* If we're cleaning up, only allow ops that affect Duet status */
	if (atomic_read(&duet_env.status) != DUET_STATUS_ON && !(flags &
	    (DUET_STATUS_START | DUET_STATUS_STOP | DUET_STATUS_REPORT))) {
		pr_err("duet_status: ops rejected during shutdown\n");
		ret = -EINVAL;
		goto done;
	}

	switch (flags) {
	case DUET_STATUS_START:
		ret = duet_bootstrap(sa->maxtasks);

		if (ret)
			pr_err("duet: failed to enable framework\n");
		else
			pr_info("duet: framework enabled\n");

		break;

	case DUET_STATUS_STOP:
		ret = duet_shutdown();

		if (ret)
			pr_err("duet: failed to disable framework\n");
		else
			pr_info("duet: framework disabled\n");

		break;

	case DUET_STATUS_REPORT:
		ret = duet_online();
		break;

	case DUET_STATUS_PRINT_BMAP:
		ret = duet_print_bmap(sa->id);
		break;

	case DUET_STATUS_PRINT_ITEM:
		ret = duet_print_item(sa->id);
		break;

	case DUET_STATUS_PRINT_LIST:
		ret = duet_print_list(arg);
		goto done;

	default:
		pr_info("duet_status: invalid flags\n");
		ret = -EINVAL;
		goto done;
	}

	if (copy_to_user(arg, sa, sizeof(*sa))) {
		pr_err("duet_status: copy_to_user failed\n");
		ret = -EINVAL;
		goto done;
	}

done:
	kfree(sa);
	return ret;
}
