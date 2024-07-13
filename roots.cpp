/*
 * Copyright (C) 2007 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <errno.h>
#include <stdlib.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <ctype.h>
#include <fcntl.h>

#include <fs_mgr.h>
#include "mtdutils/mtdutils.h"
#include "mtdutils/mounts.h"
#include "roots.h"
#include "common.h"
#include "ext4_utils/make_ext4fs.h"
extern "C" {
#include "ext4_utils/wipe.h"
#include "cryptfs.h"
}

// SPRD: include file
#include "ext4_utils/ext4_utils.h"
// SPRD: add for ubi support
#include "ubiutils/ubiutils.h"
// SPRD: add for format vfat
#include "vfat/vfat_format.h"
/*SPRD: Add block device file system check function {@ */
#include <stdio.h>
#include <string.h>
#ifdef HAVE_SYS_IOCTL_H
#include <sys/ioctl.h>
#endif
#include "ext2fs/ext2fs.h"
#include "blkid/blkid.h"
#include "blkid/blkidP.h"
/* @} */
static struct fstab *fstab = NULL;

extern struct selabel_handle *sehandle;
/*SPRD: Add block device file system check function {@ */
int get_block_fs(char *path, char* fs) {
    blkid_cache cache = NULL;
    if (blkid_get_cache(&cache, NULL) < 0) {
        LOGE("get cache fail \n");
        return -1;
    }

    blkid_dev dev = blkid_get_dev(cache, path,BLKID_DEV_NORMAL);
    if(dev && dev->bid_type) {
        strcpy(fs, dev->bid_type);
        LOGE("%s fs is %s \n", path, fs);
        blkid_put_cache(cache);
        return 0;
    }
    blkid_put_cache(cache);
    return -1;
}
/* @} */
void load_volume_table()
{
    int i;
    int ret;

    fstab = fs_mgr_read_fstab("/etc/recovery.fstab");
    if (!fstab) {
        LOGE("failed to read /etc/recovery.fstab\n");
        return;
    }

    ret = fs_mgr_add_entry(fstab, "/tmp", "ramdisk", "ramdisk");
    if (ret < 0 ) {
        LOGE("failed to add /tmp entry to fstab\n");
        fs_mgr_free_fstab(fstab);
        fstab = NULL;
        return;
    }

    printf("recovery filesystem table\n");
    printf("=========================\n");
    for (i = 0; i < fstab->num_entries; ++i) {
        Volume* v = &fstab->recs[i];
        printf("  %d %s %s %s %lld\n", i, v->mount_point, v->fs_type,
               v->blk_device, v->length);
    }
    printf("\n");
}

Volume* volume_for_path(const char* path) {
    return fs_mgr_get_entry_for_mount_point(fstab, path);
}

int ensure_path_mounted(const char* path) {
    Volume* v = volume_for_path(path);

    /* SPRD: add fota support { */
    #ifdef FOTA_UPDATE_SUPPORT
      if (strncmp(path, "/fotaupdate/", 12) == 0) {
        return 0;
      }
    #endif
    /* } */

    if (v == NULL) {
        LOGE("unknown volume for path [%s]\n", path);
        return -1;
    }
    if (strcmp(v->fs_type, "ramdisk") == 0) {
        // the ramdisk is always mounted.
        return 0;
    }

    int result;
    result = scan_mounted_volumes();
    if (result < 0) {
        LOGE("failed to scan mounted volumes\n");
        return -1;
    }

    const MountedVolume* mv =
        find_mounted_volume_by_mount_point(v->mount_point);
    if (mv) {
        // volume is already mounted
        return 0;
    }

    mkdir(v->mount_point, 0755);  // in case it doesn't already exist

    if (strcmp(v->fs_type, "yaffs2") == 0) {
        // mount an MTD partition as a YAFFS2 filesystem.
        mtd_scan_partitions();
        const MtdPartition* partition;
        partition = mtd_find_partition_by_name(v->blk_device);
        if (partition == NULL) {
            LOGE("failed to find \"%s\" partition to mount at \"%s\"\n",
                 v->blk_device, v->mount_point);
            return -1;
        }
        return mtd_mount_partition(partition, v->mount_point, v->fs_type, 0);
/* SPRD: add for ubifs @{ */
    } else if (strcmp(v->fs_type, "ubifs") == 0) {
        return ubi_mount(v->blk_device, v->mount_point, v->fs_type, 0);
/* @} */
    } else if (strcmp(v->fs_type, "ext4") == 0 ||
               strcmp(v->fs_type, "squashfs") == 0 ||
               strcmp(v->fs_type, "vfat") == 0) {
/* SPRD: add support for some sdcard can not get ready immediately
@orig
        result = mount(v->blk_device, v->mount_point, v->fs_type,
                       v->flags, v->fs_options);
        if (result == 0) return 0;
 @{ */
/***************************************************************************/
#define SLEEP_SDCARD 1
#define TRY_MOUNT_TIMES 8
        int tryCount = 0;
        char *dev_buf;
        int path_length = 0;
        struct stat s;
        int i = 0;
        char block_fs_type[16];
        dev_buf = strdup(v->blk_device);
        sleep(SLEEP_SDCARD);
        for(i = 1;i<6;){
            if(stat(dev_buf, &s)==0)
                break;
            else {
                i++;
                path_length = strlen(dev_buf);
                sprintf(dev_buf + path_length -1, "%d\0", i);
            }
        }
        if(i==6){
            path_length = strlen(dev_buf);
            dev_buf[path_length -2] = '\0';
        }
        if(get_block_fs(dev_buf, block_fs_type)) {
            strcpy(block_fs_type, v->fs_type);
        }
        while(tryCount++ < TRY_MOUNT_TIMES){
            if( mount(dev_buf, v->mount_point, block_fs_type, v->flags, v->fs_options))
                sleep(SLEEP_SDCARD);
            else
                return 0;
        }
#undef SLEEP_SDCARD
#undef TRY_MOUNT_TIMES
/* @} */


        LOGE("failed to mount %s (%s)\n", v->mount_point, strerror(errno));
        return -1;
    }

    LOGE("unknown fs_type \"%s\" for %s\n", v->fs_type, v->mount_point);
    return -1;
}

int ensure_path_unmounted(const char* path) {
    Volume* v = volume_for_path(path);

    /* SPRD: add fota support { */
    #ifdef FOTA_UPDATE_SUPPORT
      if (strncmp(path, "/fotaupdate/", 12) == 0) {
        return 0;
      }
    #endif
    /* } */


    if (v == NULL) {
        LOGE("unknown volume for path [%s]\n", path);
        return -1;
    }
    if (strcmp(v->fs_type, "ramdisk") == 0) {
        // the ramdisk is always mounted; you can't unmount it.
        return -1;
    }

    int result;
    result = scan_mounted_volumes();
    if (result < 0) {
        LOGE("failed to scan mounted volumes\n");
        return -1;
    }

    const MountedVolume* mv =
        find_mounted_volume_by_mount_point(v->mount_point);
    if (mv == NULL) {
        // volume is already unmounted
        return 0;
    }

    return unmount_mounted_volume(mv);
}

static int exec_cmd(const char* path, char* const argv[]) {
    int status;
    pid_t child;
    if ((child = vfork()) == 0) {
        execv(path, argv);
        _exit(-1);
    }
    waitpid(child, &status, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        LOGE("%s failed with status %d\n", path, WEXITSTATUS(status));
    }
    return WEXITSTATUS(status);
}

int format_volume(const char* volume) {
    Volume* v = volume_for_path(volume);
    if (v == NULL) {
        LOGE("unknown volume \"%s\"\n", volume);
        return -1;
    }
    if (strcmp(v->fs_type, "ramdisk") == 0) {
        // you can't format the ramdisk.
        LOGE("can't format_volume \"%s\"", volume);
        return -1;
    }
    if (strcmp(v->mount_point, volume) != 0) {
        LOGE("can't give path \"%s\" to format_volume\n", volume);
        return -1;
    }

    if (ensure_path_unmounted(volume) != 0) {
        LOGE("format_volume failed to unmount \"%s\"\n", v->mount_point);
        return -1;
    }

    if (strcmp(v->fs_type, "yaffs2") == 0 || strcmp(v->fs_type, "mtd") == 0) {
        mtd_scan_partitions();
        const MtdPartition* partition = mtd_find_partition_by_name(v->blk_device);
        if (partition == NULL) {
            LOGE("format_volume: no MTD partition \"%s\"\n", v->blk_device);
            return -1;
        }

        MtdWriteContext *write = mtd_write_partition(partition);
        if (write == NULL) {
            LOGW("format_volume: can't open MTD \"%s\"\n", v->blk_device);
            return -1;
        } else if (mtd_erase_blocks(write, -1) == (off_t) -1) {
            LOGW("format_volume: can't erase MTD \"%s\"\n", v->blk_device);
            mtd_write_close(write);
            return -1;
        } else if (mtd_write_close(write)) {
            LOGW("format_volume: can't close MTD \"%s\"\n", v->blk_device);
            return -1;
        }
        return 0;
    }

    if (strcmp(v->fs_type, "ext4") == 0 || strcmp(v->fs_type, "f2fs") == 0) {
        // if there's a key_loc that looks like a path, it should be a
        // block device for storing encryption metadata.  wipe it too.
        if (v->key_loc != NULL && v->key_loc[0] == '/') {
            LOGI("wiping %s\n", v->key_loc);
            int fd = open(v->key_loc, O_WRONLY | O_CREAT, 0644);
            if (fd < 0) {
                LOGE("format_volume: failed to open %s\n", v->key_loc);
                return -1;
            }
            wipe_block_device(fd, get_file_size(fd));
            close(fd);
        }

        ssize_t length = 0;
        if (v->length != 0) {
            length = v->length;
        } else if (v->key_loc != NULL && strcmp(v->key_loc, "footer") == 0) {
            length = -CRYPT_FOOTER_OFFSET;
        }
        int result;
        if (strcmp(v->fs_type, "ext4") == 0) {
	    #ifdef BOARD_USERDATAIMAGE_PARTITION_SIZE
	    if(strcmp(volume, "/data") == 0){
		length = BOARD_USERDATAIMAGE_PARTITION_SIZE;
	    }
	    #endif
            result = make_ext4fs(v->blk_device, length, volume, sehandle);
        } else {   /* Has to be f2fs because we checked earlier. */
            if (v->key_loc != NULL && strcmp(v->key_loc, "footer") == 0 && length < 0) {
                LOGE("format_volume: crypt footer + negative length (%zd) not supported on %s\n", length, v->fs_type);
                return -1;
            }
            if (length < 0) {
                LOGE("format_volume: negative length (%zd) not supported on %s\n", length, v->fs_type);
                return -1;
            }
            char *num_sectors;
            if (asprintf(&num_sectors, "%zd", length / 512) <= 0) {
                LOGE("format_volume: failed to create %s command for %s\n", v->fs_type, v->blk_device);
                return -1;
            }
            const char *f2fs_path = "/sbin/mkfs.f2fs";
            const char* const f2fs_argv[] = {"mkfs.f2fs", "-t", "-d1", v->blk_device, num_sectors, NULL};

            result = exec_cmd(f2fs_path, (char* const*)f2fs_argv);
            free(num_sectors);
        }
        if (result != 0) {
            LOGE("format_volume: make %s failed on %s with %d(%s)\n", v->fs_type, v->blk_device, result, strerror(errno));
            return -1;
        }
        return 0;
    }

    /* SPRD: add for ubifs @{ */
    if (strcmp(v->fs_type, "ubifs") == 0) {
        int result = ubi_update(v->blk_device, 0, volume);
        if (result != 0) {
            LOGE("format_volume: make_ubifs failed on %s\n", v->blk_device);
            return -1;
        }
        return 0;
    }
    /* @} */

    /* SPRD: add for format vfat @{ */
    if (strcmp(v->fs_type, "vfat") == 0) {
        int result = format_vfat(v->blk_device, 0, 0);
        if (result != 0) {
            LOGE("format_volume: format_vfat failed on %s\n", v->blk_device);
            return -1;
        }
        return 0;
    }
    /* @} */

    LOGE("format_volume: fs_type \"%s\" unsupported\n", v->fs_type);
    return -1;
}

int setup_install_mounts() {
    if (fstab == NULL) {
        LOGE("can't set up install mounts: no fstab loaded\n");
        return -1;
    }
    for (int i = 0; i < fstab->num_entries; ++i) {
        Volume* v = fstab->recs + i;

        if (strcmp(v->mount_point, "/tmp") == 0 ||
            strcmp(v->mount_point, "/cache") == 0) {
            if (ensure_path_mounted(v->mount_point) != 0) {
                LOGE("failed to mount %s\n", v->mount_point);
                return -1;
            }
        }
    /* SPRD: fix cache to small, use sdcard @{ */
        else if (strcmp(v->mount_point, "/storage/sdcard0") == 0 ||
                strcmp(v->mount_point, "/storage/sdcard1") == 0) {
                ensure_path_mounted(v->mount_point);
        }
    /*@}*/
       else{
          if (ensure_path_unmounted(v->mount_point) != 0) {
                LOGE("failed to unmount %s\n", v->mount_point);
                return -1;
          }
       }
    }
    return 0;
}
