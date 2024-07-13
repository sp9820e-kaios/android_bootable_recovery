#ifdef WIN32
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <windows.h>
#define old_path "D:\\juan.wu\\nvmerge\\tdnvitem_old.bin"
#define new_path "D:\\juan.wu\\nvmerge\\tdnvitem_new.bin"
#define out_path "D:\\juan.wu\\nvmerge\\tdnvitem_out.bin"
#define cfg_path "D:\\juan.wu\\nvmerge\\nvmerge.cfg"
#define NVMERGE_TRACE  printf
#else
#define LOG_TAG "NVMERGE"
//#include <cutils/log.h>
#define NVMERGE_TRACE  printf
#endif

typedef unsigned char		BOOLEAN;
typedef unsigned char		uint8;
typedef unsigned short		uint16;
typedef unsigned  int		uint32;

typedef signed char		int8;
typedef signed short		int16;
typedef signed int		int32;

#define TRUE     1
#define FALSE    0
#define NV_SIZE_MAX	0x80000
#define BACKUP_NUM_MAX   100
#define INVALID_ID   0xffff

typedef struct _NVITEM_CFG { /* Information of every item */
	uint32		       id;
	char               name[50];
} NVITEM_CFG;

//#define NV_SIZE   	0x40000

