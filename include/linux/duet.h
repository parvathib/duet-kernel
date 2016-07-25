/*
 * Defs necessary for Duet hooks
 *
 * Author: George Amvrosiadis <gamvrosi@gmail.com>
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
#ifndef _DUET_H
#define _DUET_H

/*
 * Duet hooks into the page cache to monitor four types of events:
 *   ADDED:	a page __descriptor__ was inserted into the page cache
 *   REMOVED:	a page __describptor__ was removed from the page cache
 *   DIRTY:	page's dirty bit was set
 *   FLUSHED:	page's dirty bit was cleared
 */
#define DUET_PAGE_ADDED		0x0001
#define DUET_PAGE_REMOVED	0x0002
#define DUET_PAGE_DIRTY		0x0004
#define DUET_PAGE_FLUSHED	0x0008

#define DUET_HOOK(funp, evt, data) \
	do { \
		rcu_read_lock(); \
		funp = rcu_dereference(duet_hook_fp); \
		if (funp) \
			funp(evt, (void *)data); \
		rcu_read_unlock(); \
	} while (0)

/* Hook function pointer initialized by the Duet framework */
typedef void (duet_hook_t) (__u16, void *);
extern duet_hook_t *duet_hook_fp;

#endif /* _DUET_H */
