/*
 * Create by Spreadst for secure boot
 */

#ifndef _SPRD_SECURE_BOOT_VERIFIER_H
#define _SPRD_SECURE_BOOT_VERIFIER_H

#define VARIFY_CONTENT_TYPE_INV    -1  //invalid
#define VARIFY_CONTENT_TYPE_FILE    1
#define VARIFY_CONTENT_TYPE_DATA    2

#define VARIFY_TYPE_INV   -1  //invalid
#define VARIFY_TYPE_NON    0  //node
#define VARIFY_TYPE_VLR    1
#define VARIFY_TYPE_BSC    2
#define VARIFY_TYPE_SPL1    3

#define SECURE_BOOT_VERIFY_SUCCESS    0
#define SECURE_BOOT_VERIFY_FAILURE    1

#define BOOT_INFO_SIZE (512)
#define KEY_INFO_SIZ    (512)
#define VLR_INFO_SIZ    (512)
#define VLR_INFO_OFF    (512)

#define CONFIG_BOOTINFO_LENGTH  (0x200)  /* 512 Bytes*/

#define CONFIG_SPL_LOAD_LEN   (0xC00)  //3k
//#define SPL2_DATA_LEN   (0x5000)   //20k
#define SPL2_DATA_LEN   (0x7800)   //30k

//#define CONFIG_SPL_HASH_LEN  (0xC00)
#define CONFIG_SPL_HASH_LEN  (1024)
#define BOOTLOADER_HEADER_OFFSET (0x20)

#define MIN_UNIT	(512)
#define HEADER_NAME "SPRD-SECUREFLAG"

#define VLR_NAME (0x3A524C56)
#define PUK_NAME (0x3A4B5550)
#define CODE_NAME (0x45444F43)

typedef struct{
	uint32_t tag_name;
	uint32_t  tag_offset;
	uint32_t  tag_size;
	uint8_t reserved[4];
}tag_info_t;

typedef struct{
	uint8_t header_magic[16];
	uint32_t  header_ver;
	uint32_t  tags_number;
	uint8_t header_ver_padding[8];
	tag_info_t tag[3];
	uint8_t reserved[432];
}header_info_t;

typedef struct
{
        uint32_t mVersion; // 1
        uint32_t mMagicNum; // 0xaa55a5a5
        uint32_t mCheckSum;//check sum value for bootloader header
        uint32_t mHashLen;//word length
        uint32_t mSectorSize; // sector size 1-1024
        uint32_t mAcyCle; // 0, 1, 2
        uint32_t mBusWidth; // 0--8 bit, 1--16bit
        uint32_t mSpareSize; // spare part size for one sector
        uint32_t mEccMode; // 0--1bit, 1-- 2bit, 2--4bit, 3--8bit, 4--12bit, 5--16bit, 6--24bit
        uint32_t mEccPostion; // ECC postion at spare part
        uint32_t mSectPerPage; // sector per page
        uint32_t mSinfoPos;
        uint32_t mSinfoSize;
        uint32_t mECCValue[27];
        uint32_t mPgPerBlk;
        uint32_t mImgPage[5];
} NBLHeader;

#ifdef __cplusplus
extern "C" {
#endif

int file_read(int fd, unsigned char *buf, int len, const char *filename);
int get_secure_boot_verify_type(const char *secureboot);
int sprd_secure_boot_verify(int verify_type, int content_type, unsigned char *data, unsigned int size, const char *target,
        unsigned char *previous_data, int previous_size, int previous_type);
int compare_harsh(unsigned char *verify_data);
int get_spl_hash(unsigned char *data, void* hash_data);
#ifdef __cplusplus
}
#endif

#endif  /* _SPRD_SECURE_BOOT_VERIFIER_H */
