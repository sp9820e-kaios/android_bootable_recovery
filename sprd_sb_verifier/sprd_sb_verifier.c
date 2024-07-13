/*
 * Create by Spreadst for secure boot
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdio.h>
#include <pthread.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
//SPRD: add header
#include <errno.h>
#include "sec_boot.h"
#include "sha1_32.h"

#include "sprd_sb_verifier.h"

#include "sprd_efuse_hw.h"

int compare_hash(unsigned char *verify_data);

typedef struct verify_info_struct {
    unsigned char *data;
    int size;
    int type;
    unsigned char *previous_data;
    int previous_size;
    int previous_type;
    int res;
    pthread_cond_t *cond;
    pthread_mutex_t *mutex;
} verify_info_t;

static int printf_with_time(const char *fmt, ...)
{
    int ret;
    va_list ap;
    struct timeval now;

    gettimeofday(&now, NULL);
    printf("%d.%06d:", now.tv_sec, now.tv_usec);

    va_start(ap, fmt);
    ret = vfprintf(stdout, fmt, ap);
    va_end(ap);
    return (ret);
}

static int secure_header_parser(const char *header_addr, int verify_type)
{
    if(verify_type == VARIFY_TYPE_BSC || strcmp(header_addr, HEADER_NAME) == 0 )
        return 1;
    else
        return 0;
}

static unsigned char *get_code_addr(unsigned char *header_addr, int verify_type, int previous_type)
{
    unsigned char *addr = NULL;
    int i=0;
    header_info_t *header_p = (header_info_t *)header_addr;

    if (verify_type == VARIFY_TYPE_BSC){
        addr = header_addr+BOOT_INFO_SIZE+KEY_INFO_SIZ;
        return addr;
    }

    for(i=0;i<header_p->tags_number;i++)
    {
        if(header_p->tag[i].tag_name == CODE_NAME)
        {
            addr = header_addr + (header_p->tag[i].tag_offset)*MIN_UNIT;
            break;
        }
    }
    if(previous_type == VARIFY_TYPE_BSC){
        printf("get_code_addr VARIFY_TYPE_BSC\n");
        addr -= CONFIG_BOOTINFO_LENGTH;
    }
    return addr;
}

static unsigned char * get_vlr_addr(unsigned char *header_addr, int verify_type)
{
    int i=0;
    unsigned char * addr = NULL;
    header_info_t *header_p = (header_info_t *)header_addr;

    if (verify_type == VARIFY_TYPE_BSC){
        //addr = header_addr + CONFIG_SPL_LOAD_LEN + SPL2_DATA_LEN + KEY_INFO_SIZ;
        addr = header_addr + BOOT_INFO_SIZE + KEY_INFO_SIZ + SPL2_DATA_LEN+KEY_INFO_SIZ;
        return addr;
    }

    for(i=0;i<header_p->tags_number;i++)
    {
        if(header_p->tag[i].tag_name == VLR_NAME)
        {
            addr = header_addr + (header_p->tag[i].tag_offset)*MIN_UNIT;
            break;
        }
    }
    return addr;
}

static unsigned char * get_puk_addr(unsigned char *header_addr, int verify_type)
{
    unsigned char * addr = NULL;
    int i=0;
    int size;
    header_info_t *header_p = (header_info_t *)header_addr;

    if (verify_type == VARIFY_TYPE_SPL1){
        //addr = header_addr+CONFIG_SPL_LOAD_LEN-KEY_INFO_SIZ;
        addr = header_addr+BOOT_INFO_SIZE;
        return addr;
    }
    if (verify_type == VARIFY_TYPE_BSC){
        //addr = header_addr+CONFIG_SPL_LOAD_LEN-KEY_INFO_SIZ;
        //addr = header_addr+CONFIG_SPL_LOAD_LEN+SPL2_DATA_LEN;
        addr = header_addr+BOOT_INFO_SIZE+KEY_INFO_SIZ+SPL2_DATA_LEN;
        return addr;
    }
    for(i=0;i<header_p->tags_number;i++)
    {
        if(header_p->tag[i].tag_name == PUK_NAME)
        {
            addr = (uint8_t*)header_p + (header_p->tag[i].tag_offset)*MIN_UNIT;
            break;
        }
    }
    return addr;
}

static void *secure_boot_verify(void *data)
{
    int ret;
    unsigned char *verify_data;
    int verify_size;
    int verify_type;
    unsigned char *previous_verify_data;
    int previous_verify_size;
    int previous_verify_type;
    unsigned char * vlr_addr;
    unsigned char * puk_addr;
    unsigned char * code_addr;
    unsigned int code_size = 0;
    verify_info_t *verify_info = (verify_info_t *)data;

    if (verify_info == NULL) {
        goto done;
    }

    verify_data = verify_info->data;
    verify_size = verify_info->size;
    verify_type = verify_info->type;
    previous_verify_data = verify_info->previous_data;
    previous_verify_size = verify_info->previous_size;
    previous_verify_type = verify_info->previous_type;

    printf("secure_boot_verify\n");

    if (!secure_header_parser((const char*)verify_data, verify_type)){
        verify_info->res = -1;
        goto done;
    }

    if (verify_type == VARIFY_TYPE_BSC) {
        ret = compare_hash(verify_data);
        if(ret){
            verify_info->res = -1;
            goto done;
        }
    }

    if (verify_type == VARIFY_TYPE_BSC) {
        previous_verify_data = verify_data;
        previous_verify_type = VARIFY_TYPE_SPL1;
    }

    //puk_addr = get_puk_addr(verify_data, verify_type);
    puk_addr = get_puk_addr(previous_verify_data, previous_verify_type);
    vlr_addr = get_vlr_addr(verify_data, verify_type);
    code_addr = get_code_addr(verify_data, verify_type, previous_verify_type);
    if (verify_type == VARIFY_TYPE_BSC){
        code_size = SPL2_DATA_LEN + KEY_INFO_SIZ;
    } else {
        code_size = ((vlr_info_t*)vlr_addr)->length;
    }

    printf_with_time("secure_check begin\n");
    printf("puk_addr=0x%08x, vlr_addr=0x%08x, code_addr=0x%08x, code_size=0x%08x\n", puk_addr, vlr_addr, code_addr, code_size);
    secure_check(code_addr, code_size, vlr_addr, puk_addr);
    printf_with_time("secure_check end\n");

    verify_info->res = 0;
done:
    pthread_mutex_lock(verify_info->mutex);
    pthread_cond_signal(verify_info->cond);
    pthread_mutex_unlock(verify_info->mutex);

    return NULL;
}

int file_read(int fd, unsigned char *buf, int len, const char *filename)
{
    int read_len = 0;

    while (len) {
        int ret = read(fd, buf, len);
        if (ret < 0) {
            if (errno == EINTR) {
                continue;
            }
            printf("cannot read %d bytes from file \"%s\": %s\n",
                              len, filename, strerror(errno));
            break;
        }

        if (ret == 0) {
            printf("cannot read more bytes from file \"%s\"\n", filename);
            break;
        }

        len -= ret;
        buf += ret;
        read_len += ret;
    }

    return read_len;
}

int get_secure_boot_verify_type(const char *secureboot)
{
    int verify_type = VARIFY_TYPE_INV;
    if (secureboot == NULL) {
        return VARIFY_TYPE_NON;
    }
    if (strcmp(secureboot, "vlr") == 0) {
        verify_type = VARIFY_TYPE_VLR;
    } else if (strcmp(secureboot, "bsc") == 0) {
        verify_type = VARIFY_TYPE_BSC;
    } else {
        verify_type = VARIFY_TYPE_INV;
    }
    return verify_type;
}

static int check_verify_and_content_type(int verify_type, int content_type)
{
    int res = 0;
    switch (verify_type) {
        case VARIFY_TYPE_VLR:
        case VARIFY_TYPE_BSC:
        case VARIFY_TYPE_NON:
            break;
        default:
            res |= 1;
            break;
    }
    switch (content_type) {
        case VARIFY_CONTENT_TYPE_FILE:
        case VARIFY_CONTENT_TYPE_DATA:
            break;
        default:
            res |= 2;
            break;
    }
    return res;
}

static void maketimeout(struct timespec *tsp, long minutes)
{
    struct timeval now;
    /* get the current time */
    gettimeofday(&now, NULL);
    tsp->tv_sec = now.tv_sec + minutes * 60;
    tsp->tv_nsec = now.tv_usec *1000; /* usec to nsec*/
}

int sprd_secure_boot_verify(int verify_type, int content_type, unsigned char *data, unsigned int size, const char *target,
        unsigned char *previous_data, int previous_size, int previous_type)
{
    int verify_res = SECURE_BOOT_VERIFY_FAILURE;
    unsigned char *verify_data = NULL;
    unsigned int verify_size = 0;
    unsigned char *real_data = NULL;
    unsigned int real_data_size = 0;
    unsigned char *vlr_info = NULL;
    unsigned char *puk_adr = NULL;
    int res = 0, wait_res = 0;

    printf("secure_boot_verify(%d, %d, %d) for target [%s]\n", verify_type, previous_type, content_type, target);

    if (check_verify_and_content_type(verify_type, content_type)) {
        printf("verify type \'%d\' or content type \'%d\' is invalid or unknown\n", verify_type, content_type);
        return verify_res;
    }

    if (verify_type == VARIFY_TYPE_NON)
        return SECURE_BOOT_VERIFY_SUCCESS;

    if (content_type == VARIFY_CONTENT_TYPE_DATA) {
        verify_data = data;
        verify_size = size;
    } else if (content_type == VARIFY_CONTENT_TYPE_FILE) {
        char* filename = (char*)data;
        int fd = open(filename, O_RDONLY);
        if (fd <= 0) {
            printf("can't open %s: %s\n",
                   filename, strerror(errno));
            goto done;
        }

        struct stat stat_for_size;
        int res = fstat(fd, &stat_for_size);
        if (res < 0) {
            printf("can't stat %s: %s\n",
                   filename, strerror(errno));
            goto done;
        }
        int file_size = stat_for_size.st_size;
        verify_data = (unsigned char *)malloc(file_size);
        verify_size = file_read(fd, verify_data, file_size, filename);
        if (verify_size < file_size) {
            printf("can't read enough data form %s: %s\n",
                   filename, strerror(errno));
            goto done;
        }
        close(fd);
    }

    verify_info_t verify_info;
    verify_info.data = verify_data;
    verify_info.size = verify_size;
    verify_info.type = verify_type;
    verify_info.previous_data = previous_data;
    verify_info.previous_size = previous_size;
    verify_info.previous_type = previous_type;
    verify_info.res = -2;

    pthread_cond_t verify_cond;
    pthread_mutex_t verify_mutex;
    pthread_cond_init(&verify_cond, NULL);
    pthread_mutex_init(&verify_mutex, NULL);
    verify_info.cond = &verify_cond;
    verify_info.mutex = &verify_mutex;

    struct timespec wait_time;

    printf_with_time("create thread\n");
    pthread_t verify_thread;
    res = pthread_create(&verify_thread, NULL, secure_boot_verify, &verify_info);
    if (res) {
        printf("failed to start thread to verify, error=%d\n", res);
        goto thread_error;
    }
    // wait for verify over
    printf_with_time("begin to wait thread\n");
    pthread_mutex_lock(&verify_mutex);
    maketimeout(&wait_time, 1); // wait for 1 minute
    wait_res = pthread_cond_timedwait(&verify_cond, &verify_mutex, &wait_time);
    pthread_mutex_unlock(&verify_mutex);
    printf_with_time("wait thread over\n");

    if (wait_res == 0) {
        if (verify_info.res == 0) {
            verify_res = SECURE_BOOT_VERIFY_SUCCESS;
        } else {
            printf("verify error, res is %d.\n", verify_info.res);
        }
    } else if (ETIMEDOUT == wait_res) {
        printf_with_time("wait verify timed out!!!\n");
    }
    //pthread_cancel(verify_thread);

thread_error:
    pthread_cond_destroy(&verify_cond);
    pthread_mutex_destroy(&verify_mutex);
done:
    if (content_type == VARIFY_CONTENT_TYPE_FILE) {
        printf("free data\n");
        if (verify_data) free(verify_data);
        if (verify_info.previous_data) free(verify_info.previous_data);
    }

    return verify_res;
}

int sprd_get_spl_hash(unsigned char *data, void* hash_data)
{
    NBLHeader *header;
    int len;
    unsigned char *spl_data;
    int size = CONFIG_SPL_HASH_LEN;
    sha1context_32       sha;

    printf("sprd_get_spl_hash enter\n");

    spl_data = (unsigned char *)malloc(size);
    if (!spl_data){
        return -1;
    }

    memcpy(spl_data, data, size);

    header = (NBLHeader *)((unsigned char*)spl_data+BOOTLOADER_HEADER_OFFSET);
    len = header->mHashLen;
    /*clear header*/
    memset(header,0,sizeof(NBLHeader));
    header->mHashLen = len;
    printf("sprd_get_spl_hash spl hash len=%d\n",header->mHashLen*4);

    //ret = cal_sha1(spl_data,size,hash_data);
    SHA1Reset_32(&sha);
    SHA1Input_32(&sha, (uint32_t*)spl_data, size>>2);
    SHA1Result_32(&sha, hash_data);

    if (spl_data)
        free(spl_data);

    return 0;
}

int compare_hash(unsigned char *verify_data){
    int i;
    int ret;
    int index = 0;
    unsigned char spl_buf[64] = {0};
    unsigned harsh_data_buf[8] = {0};
    void *harsh_data = harsh_data_buf;
    unsigned char hash_buf[41] = {0};
    unsigned int spl_value[5] = {0};
    unsigned int efuse_value[5] = {0};

    ret = sprd_get_spl_hash(verify_data, harsh_data);
    if(!ret){
        sprintf(spl_buf, "%08x%08x%08x%08x%08x", *(uint32_t*)harsh_data, *(uint32_t*)(harsh_data+4),\
                *(uint32_t*)(harsh_data+8), *(uint32_t*)(harsh_data+12),*(uint32_t*)(harsh_data+16));
        printf("spl hash = %s\n", spl_buf);
    }else{
        printf("sprd_get_spl_hash failed\n");
        return -1;
    }

    ret = efuse_hash_read(hash_buf, sizeof(hash_buf));
    if(ret){
        printf("efuse hash = %s\n", hash_buf);
        for (i = 0; i < 40; i += 8) {
            char buf[9] = {0};
            memset(buf, 0, sizeof(buf));
            strncpy((char*)buf, (char*)&hash_buf[i], 8);
            buf[8]='\0';
            efuse_value[index] = (unsigned int)(strtoul(buf, 0, 16));
            memset(buf, 0, sizeof(buf));
            strncpy((char*)buf, (char*)&spl_buf[i], 8);
            buf[8]='\0';
            spl_value[index] = (unsigned int)(strtoul(buf, 0, 16));
            index++;
        }

        for (i = 0; i < 5; i++) {
            spl_value[i] &= (~0x80000000);    //BIT31
            efuse_value[i] &= (~0x80000000);    //BIT31
        }

        if((efuse_value[0] == spl_value[0]) && (efuse_value[1] == spl_value[1]) && (efuse_value[2] == spl_value[2])
            &&(efuse_value[3] == spl_value[3]) && (efuse_value[4] == spl_value[4])){
            printf("compare_harsh ok\n");
            return 0;
        }else{
            printf("compare_hash failed\n");
            return -1;
        }
    }else{
        printf("efuse_hash_read failed\n");
        return -1;
    }

    return 0;
}
