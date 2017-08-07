DEBUG = y
# Add the debugging flag (or not) to CFLAGS
ifeq ($(DEBUG),y)
  DEBFLAGS = -O -g -DNOTIFY_DEBUG # "-O" is needed to expand inlines
else
  DEBFLAGS = -O2
endif
subdir-ccflags-$y := $(DEBFLAGS)

obj-$(CONFIG_FSNOTIFY)		+= fsnotify.o notification.o group.o mark.o \
				   fdinfo.o

obj-y			+= dnotify/
obj-y			+= inotify/
obj-y			+= fanotify/
