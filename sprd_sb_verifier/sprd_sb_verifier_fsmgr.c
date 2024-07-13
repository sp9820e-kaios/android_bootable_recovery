/*
 * Create by Spreadst for secure boot
 */
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include <fs_mgr.h>
#include <linux/fs.h>
//SPRD: add header
#include <errno.h>
#include "mtdutils.h"
#include "sprd_sb_verifier_fsmgr.h"
#include "../ubiutils/ubiutils.h"
#include "sprd_sb_verifier.h"

struct MtdReadContext {
    const MtdPartition *partition;
    char *buffer;
    size_t consumed;
    int fd;
};

static struct fstab *fstab = NULL;
static int mtd_partitions_scanned = 0;

/*
 * get secure boot verify type from device path
 */
static void load_volume_table()
{
    int i;
    int ret;

    fstab = fs_mgr_read_fstab("/etc/recovery.fstab");
    if (!fstab) {
        printf("failed to read /etc/recovery.fstab\n");
        return;
    }
}

/*
 * get secure boot verify type from device path
 */
const char *get_secureboot_for_device(const char *device)
{
    int i;
    const char *secureboot = NULL;

    if (!fstab) {
        load_volume_table();
        if (!fstab)
            return "";
    }

    for (i = 0; i < fstab->num_entries; i++) {
        if (strcmp(device, fstab->recs[i].blk_device) == 0) {
            secureboot = fstab->recs[i].secure_boot;
            break;
        }
    }

    printf("get_secureboot_for_device(%s) return \'%s\'\n", device, secureboot);
    return secureboot;
}

void get_previous_secureboot_for_device(char *device, char **previous_dev,
          char **previous_type, char **previous_fstype)
{
    int i;
    int j;
    char *previous_mountpoint = NULL;

    printf("get_previous_secureboot_for_device enter\n");

    if (!fstab) {
        load_volume_table();
        if (!fstab)
            return;
    }

    for (i = 0; i < fstab->num_entries; i++) {
        if (strcmp(device, fstab->recs[i].blk_device) == 0) {
            previous_mountpoint = fstab->recs[i].previous_mountpoint;
            if(previous_mountpoint == NULL){
                return;
            }else{
                for(j = 0; j < fstab->num_entries; j++){
                    if(strcmp(previous_mountpoint, fstab->recs[j].mount_point) == 0){
                        *previous_dev = fstab->recs[j].blk_device;
                        *previous_type = fstab->recs[j].secure_boot;
                        *previous_fstype = fstab->recs[j].fs_type;
                        break;
                    }
                }
            }
            break;
        }
    }

    printf("device = %s, previous_dev = %s, previous_type = %s, previous_fstype = %s\n",
                 device, *previous_dev, *previous_type, *previous_fstype);

    return;
}

unsigned char *get_previous_data_for_device(char *fstype, char *partition, int *size){
    int i;
    int fd;
    int ret;
    int read_len;
    long long file_size;
    int verify_size;

    unsigned char *verify_data = NULL;
    unsigned char *base_data = NULL;

    printf("get_previous_data_for_device, partition = %s, fstype = %s\n", partition, fstype);

    if(strcmp(fstype, "emmc") == 0 || strcmp(fstype, "ext4") == 0 || strcmp(fstype, "ubi") == 0 || strcmp(fstype, "ubifs") == 0){
        if(strcmp(fstype, "emmc") == 0 || strcmp(fstype, "ext4") == 0){
            fd = open(partition, O_RDONLY);
        }else if(strcmp(fstype, "ubi") == 0 || strcmp(fstype, "ubifs") == 0){
            fd = ubi_open(partition, O_RDONLY);
        }

        if (fd <= 0) {
            printf("can't open %s: %s\n",
                   partition, strerror(errno));
            goto done;
        }

        if(-1 == ioctl(fd,BLKGETSIZE64,&file_size)) {
            printf("get file size error %s: %s\n", partition, strerror(errno));
            goto done;
        }

        printf("file_size = %lld\n", file_size);
        verify_data = (unsigned char *)malloc((int)file_size);
        verify_size = file_read(fd, verify_data, (int)file_size, partition);
        printf("verify_size = %d\n", verify_size);
        if (verify_size < (int)file_size) {
            printf("can't read enough data form %s\n",partition);
            goto done;
        }
        close(fd);
    }else if(strcmp(fstype, "mtd") == 0 || strcmp(fstype, "yaffs2") == 0){
        if (!mtd_partitions_scanned) {
            mtd_scan_partitions();
            mtd_partitions_scanned = 1;
        }

        const MtdPartition* mtd = mtd_find_partition_by_name(partition);
        if (mtd == NULL) {
            printf("no mtd partition named \"%s\"\n", partition);
            return NULL;
        }

        MtdReadContext* ctx = mtd_read_partition(mtd);
        if (ctx == NULL) {
            printf("can't read mtd partition \"%s\"\n", partition);
            return NULL;
        }

        if (mtd_partition_info(mtd, &file_size, NULL, NULL)){
            printf("mtd get file size error %s: %s\n", partition, strerror(errno));
            goto done1;
        }

        printf("file_size = %lld\n", file_size);
        verify_data = (unsigned char *)malloc((int)file_size);
        verify_size = mtd_read_data(ctx, verify_data, (int)file_size);
        if (verify_size != (int)file_size) {
            printf("mtd_read_data from %s failed\n", partition);
            goto done1;
        }

    done1:
        mtd_read_close(ctx);
    }

    if(size != NULL){
        *size = verify_size;
        printf("verify_size = %d\n", verify_size);
    }

    return verify_data;

done:
    if (verify_data) free(verify_data);
    return NULL;

}
