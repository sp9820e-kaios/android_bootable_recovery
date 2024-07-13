#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
//SPRD: add header
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/mount.h>
#include "memory.h"
#include <sys/vfs.h>
#include "crc32.h"
#include "common.h"
#include "gptdata.h"


void InitializeGPTData(GPTData *pData)
{
    printf("InitializeGPTData enter!\n");
    pData->blockSize = SECTOR_SIZE;
    pData->diskSize = 0;
    pData->partitions = NULL;
    memset(pData->device, 0, sizeof(pData->device));
    pData->fd = 0;
    pData->mainCrcOk = 0;
    pData->secondCrcOk = 0;
    pData->mainPartsCrcOk = 0;
    pData->secondPartsCrcOk = 0;
    pData->mainHeader.numParts = 0;
    pData->numParts = 0;
    //SetGPTSize(NUM_GPT_ENTRIES);
    pData->backup_dir = NULL;
    pData->count = 0;
    // Initialize CRC functions...
    chksum_crc32gentab();
    return;
}


void char16tochar(uint16_t *partname, char *buffer)
{
    int i;
    //printf("char16tochar entry!\n");
    for(i = 0; i < 36; i++) {
        buffer[i] = (char )partname[i];
    }
    //printf("char16tochar :partition name %s\n", buffer);
}

int Seek(uint64_t sector, int fd) {
    uint64_t seekTo;
    uint64_t sought;
    int ret = SUCCESS;

    printf("seek eneter!\n");

    seekTo = sector * GetBlockSize(fd);
    sought = lseek64(fd, seekTo, SEEK_SET);
    if (sought != seekTo)
    {
        ret = FAILER;
    }

    return ret;
}


int OpenForRead(GPTData *pData, char *name)
{
    printf("OpenForRead enter!\n");

    //pData->fd = open(name, O_RDONLY);
    pData->fd = open(name, O_RDWR);

    if(pData->fd < 0)
    {
        printf("can't open %s, %s\n", name, strerror(errno));
        return FAILER;
    }
    return SUCCESS;
}

int LoadPartitions(GPTData *pData, char *name)
{
    int ret = 1;

    printf("LoadPartitions enter!\n");

    ret = OpenForRead(pData, name);
    if(FAILER == ret)
    {
        printf("LoadPartitions :: OpenForRead failer!\n");
        return 0;
    }
    pData->diskSize = GetDiskSize(pData->fd);
    pData->blockSize = GetBlockSize(pData->fd);

    printf("disksize = %lld, blocksize = %d\n", pData->diskSize, pData->blockSize);

    ret = ForceLoadGPTData(pData);
    if(ret == 0) {
        return ret;
    }
    return 1;
}

int GetBlockSize(int fd)
{
    int err = -1;
    int blockSize = 0;

    err = ioctl(fd, BLKSSZGET, &blockSize);
    if(err == -1)
    {
        printf("GetBlockSize error! errno = %s\n", strerror(errno));
        blockSize = SECTOR_SIZE;
    }

    return blockSize;
}

long long GetDiskSize(int fd)
{
    int err;
    long long sectors = 0;
    long long bytes = 0;
    struct stat64 st;

    long long sz;
    long long b;

    printf("GetDiskSize enter!\n");

    err = ioctl(fd, BLKGETSIZE64, &b);
    if(err <0)
    {
        printf("GetDiskSize error\n");
    }

    printf("b = %lld\n",b);
    sectors = b;
#if 0
    err = ioctl(fd, BLKGETSIZE, &sz);
    if(err)
    {
        printf("get blksize error, error = %s\n", strerror(errno));
        sectors = sz = 0;
    }
printf("GetDiskSize111 = %d\n", sz);
    if((!err) || (errno == EFBIG))
    {
        err = ioctl(fd, BLKGETSIZE64, &b);
        if (err || b == 0 || b == sz)
        {
            sectors = sz;
            printf("GetDiskSize222 = %d\n", sectors);
        }
        else
        {
            printf("GetDiskSize333 = %d\n", b);
            sectors = (b >> 9);
            printf("GetDiskSize444 = %ld\n", sectors);
        }
    }
#endif
    // Unintuitively, the above returns values in 512-byte blocks, no
    // matter what the underlying device's block size. Correct for this....
    sectors /= GetBlockSize(fd);

    // The above methods have failed, so let's assume it's a regular
    // file (a QEMU image, dd backup, or what have you) and see what
    // fstat() gives us....
    if((sectors == 0) || (err == -1))
    {
        printf("GetDiskSize all failed!\n");
        if (fstat64(fd, &st) == 0)
        {
            bytes = st.st_size;
            if (bytes % 512 != 0)
                printf("Warning: File size is not a multiple of 512 bytes! Misbehavior is likely!\n");
            sectors = bytes / 512;
        }
     }
    printf("sectors = %lld\n", sectors);
    return sectors;
}


int ForceLoadGPTData(GPTData *pData)
{
    int allOK;
    int validHeaders;
    int loadedTable = 1;

    printf("ForceLoadGPTData enter!\n");
    printf("ForceLoadGPTData :: load main header!\n");
    allOK = LoadHeader(pData, &(pData->mainHeader), pData->fd, 1, &(pData->mainCrcOk));
    printf("ForceLoadGPTData :: pData->mainCrcOk = %d\n", pData->mainCrcOk);
    if(pData->mainCrcOk && (pData->mainHeader.backupLBA < pData->diskSize))
    {
        printf("ForceLoadGPTData :: load second header, pData->mainHeader.backupLBA = %lld\n", pData->mainHeader.backupLBA);
        allOK = LoadHeader(pData, &(pData->secondHeader), pData->fd, pData->mainHeader.backupLBA, &(pData->secondCrcOk)) && allOK;
        printf("ForceLoadGPTData :: pData->secondCrcOk = %d\n", pData->secondCrcOk);
    }
    else
    {
        printf("ForceLoadGPTData :: load second header2\n");
        allOK = LoadHeader(pData, &(pData->secondHeader), pData->fd, pData->diskSize - 1, &(pData->secondCrcOk)) && allOK;
        printf("ForceLoadGPTData :: pData->secondCrcOk2 = %d\n", pData->secondCrcOk);
        if(pData->mainCrcOk && (pData->mainHeader.backupLBA >= pData->diskSize))
        {
            printf("Warning! Disk size is smaller than the main header indicates!\n");
        }
    }

    if (!allOK)
    {
        printf("ForceLoadGPTData :: GPT invalid!\n");
            return allOK;
        //state = gpt_invalid;
    }

    validHeaders = CheckHeaderValidity(pData);
    if (validHeaders > 0)
    {
        // if at least one header is OK....
        // GPT appears to be valid....
        //state = gpt_valid;

        if(validHeaders == 1)
        {
            // valid main header, invalid backup header
            printf("Caution: invalid backup GPT header, but valid main header, regenerating backup header from main header.\n");
            RebuildSecondHeader(pData);
            //state = gpt_corrupt;
            pData->secondCrcOk = pData->mainCrcOk; // Since regenerated, use CRC validity of main
        }
        else if(validHeaders == 2)
        {
            // valid backup header, invalid main header
            printf("Caution: invalid main GPT header, but valid backup, regenerating main header from second header.\n");
            RebuildMainHeader(pData);
            //state = gpt_corrupt;
            pData->mainCrcOk = pData->secondCrcOk; // Since copied, use CRC validity of backup
        }
    }
    // Figure out which partition table to load....
    // Load the main partition table, since either its header's CRC is OK or the
    // backup header's CRC is not OK....
    if(pData->mainCrcOk || !pData->secondCrcOk)
    {
        if(LoadPartitionTable(pData, &(pData->mainHeader), pData->fd) == 0)
        {
            allOK = 0;
            return allOK;
        }
    }
    return 1;
#if 0
    else
    {
        // bad main header CRC and backup header CRC is OK
        //state = gpt_corrupt;
        if(LoadPartitionTable(pdata, &(pdada->secondHeader), pData->fd))
        {
            loadedTable = 2;
            printf("Warning: Invalid CRC on main header data; loaded second partition table.\n");
        }
        else
        {
            // backup table bad, bad main header CRC, but try main table in desperation....
            if(LoadPartitionTable(pdata, &(pdada->mainHeader), pData->fd) == 0)
            {
                allOK = 0;
                loadedTable = 0;
                printf("Warning! Unable to load either main or backup partition table!\n");
            }
        }
    }
#endif
}



int ChangePartition(GPTData *pData, int partnum, int tabnum)
{
    long long origsize, changesize;
    char buffer[36];
    long long offset ;
    int i = partnum;
    char *resizepart;

    origsize = pData->partitionSize[partnum] / GetBlockSize(pData->fd);
    changesize = 2 * 1024 * pData->gpttab.changepartsize[tabnum].newsize;

    offset = changesize - origsize;
    char16tochar(pData->partitions[i].name, buffer);

    printf("changepartition:: orignsize [%lld] Sector.\n", origsize);
    printf("changepartition:: gpttab.changepartition[%d] image_size[%lld] Sector.\n", tabnum, changesize);
    printf("Changepartition:: offset %lld sector\n", offset);

    if(pData->gpttab.resizablePart == NULL) {
        resizepart = malloc (strlen("userdata") + 1);
        strcpy(resizepart, "userdata");
    } else {
        resizepart = malloc(strlen(pData->gpttab.resizablePart) + 1);
        strcpy(resizepart, pData->gpttab.resizablePart);
    }
    printf("changepartition:: changepart size from [%s] partition!\n", resizepart);
    if( offset > 0 ) {
        while(strcmp(buffer, resizepart) != 0) {
        printf("changepartition:: %lld \n", origsize);
        pData->partitions[i].firstLBA = pData->partitions[i-1].lastLBA + 1;
        pData->partitions[i].lastLBA += offset;
            i++;
            char16tochar(pData->partitions[i].name, buffer);
        }
        pData->partitions[i].firstLBA = pData->partitions[i-1].lastLBA + 1;
    }
    else {
        printf("partition size > change size!\n");
        return 1;
    }
    return 1;
}

int ChangePartitionSize(GPTData *pData)
{
    uint32_t  j;
    uint32_t i;
    char buffer[36];
    int retval;
    printf("ChangePartitionSize:: entry!\n");

    if(pData->needBackup == 0) {
        printf("ChangePartitionSize:: Don't need change!\n");
        return 1;
    }

    for(i = 0; i< pData->numParts; i++) {
        char16tochar(pData->partitions[i].name, buffer);
        for(j = 0; j < pData->gpttab.changesizecount; j++) {
            if(strcmp(buffer, pData->gpttab.changepartsize[j].partname) == 0) {
                printf("changepartitionsize:: change part: %s.\n", buffer);
                retval = ChangePartition(pData,i, j);
                if(retval == 1)
                    printf("change partition [%s] size succeed! \n", buffer);
                else {
                    printf("change partition fail!\n");
                    return 0;
                }
            }
        }
    }

    return 1;
}

uint64_t get_system_df_free(char * disk)
{
    int ret;
    if(disk == NULL) {
        return -1;
    }
    struct statfs diskInfo;
    ret = statfs(disk,&diskInfo);
    if(ret < 0) {
        printf("statfs error: %s\n", strerror(errno));
        return -1;
    }
    unsigned long long totalBlocks = diskInfo.f_bsize;
    unsigned long long freeDisk = diskInfo.f_bfree*totalBlocks;

    printf("get_system_df_free:  disktotalBlocks %lld\n", totalBlocks);
    printf("get_system_df_free:  diskfree %lld\n", freeDisk);

    return freeDisk;
}

int BackupPartition(GPTData *pData, int partNum)
{
    int fd, ret;
    int readed;
    int writed;
    long long freeDisk;
    long long partsize;
    int dirlen;
    char filepath[256];
    char temppath[256];
    char buffer[36];
    char tmp[4096];

    freeDisk = get_system_df_free(pData->backup_dir);
    if(freeDisk < -1) {
        printf("BackupParttition:: can't get disk free space!\n");
        return -1;
    }
    partsize = GetBlockSize(pData->fd) * (pData->partitions[partNum].lastLBA - pData->partitions[partNum].firstLBA + 1);
    printf("BackupParttion:: partsize %lld \n", partsize);
    if ( freeDisk <= partsize) {
        printf("BackupPartition:: SDcard don't have enough space!\n");
        return -1;
    }
    dirlen = strlen(pData->backup_dir);
    if (pData->backup_dir[dirlen -1] != '/') {
        pData->backup_dir[dirlen] = '/';
        pData->backup_dir[dirlen +1] = 0;
    }
    printf("BackupPartition:: backup_dir  %s\n", pData->backup_dir);
    strcpy(filepath, pData->backup_dir);
    char16tochar(pData->partitions[partNum].name, buffer);
    sprintf(tmp, ".bak.%s.img", buffer);
    strcat(filepath, tmp);
    printf("BackupPartition:: final filepath =%s\n", filepath);

    sprintf(temppath, "%s.bak.tmp.img",pData->backup_dir);

    fd = open(temppath,O_RDWR | O_CREAT | O_TRUNC, 0644);
    if ( fd < -1) {
        perror("BackupPartition::open file");
        return -1;
    }
    Seek(pData->partitions[partNum].firstLBA, pData->fd);

    int  readlen;
    while(partsize > 0) {
        if(partsize < 4096)
            readlen = partsize;
        else
            readlen = 4096;
        readed = read(pData->fd, tmp, readlen);
        if( (readed < 0) || (readed != readlen)) {
            printf("Backuppartition:: can't read form /dev/block/mmcblk0\n");
            return -1;
        }
        writed = write(fd, tmp, readed);
        if((writed < 0) || (readed != writed)) {
            printf("Backuppartition:: can't write to /dev/block/mmcblk1 %s\n", strerror(errno));
            return -1;
        }
        partsize -= 4096;
    }
    ret = rename(temppath, filepath);
    if(ret < 0) {
        perror("rename:");
        return -1;
    }
    uint64_t t = 1;  //if this partition have been backed up to SDcard, set the flag.
    pData->partitions[partNum].attributes |= (t << BACKUP_FLAG);
    printf("BackupPartition :: partition->attribute %lld\n", pData->partitions[partNum].attributes);
    close(fd);
    return 1;
}


int BackupCheck(GPTData *pData)
{
    uint32_t  i, j, k, t;
    long long origsize, changesize, offset;
    char buffer[36];
    char tmp[36];
    int retval = 0;

    printf("BackupCheck::entry!\n");

    for(i = 0; i < pData->numParts; i++) {
        char16tochar(pData->partitions[i].name, buffer);
        for(j = 0; j < pData->gpttab.changesizecount; j++) {
        if(strcmp(buffer, pData->gpttab.changepartsize[j].partname) == 0) {
            origsize = pData->partitionSize[i];
            changesize = 1024 * 1024 * pData->gpttab.changepartsize[j].newsize;
            offset = changesize - origsize;
            printf("BackupCheck:offset = %lld\n", offset);
            if(offset > 0) {
                for(k = i + 1; k < pData->numParts; k++) {
                    char16tochar(pData->partitions[k].name, tmp);
                    for(t = 0; t < pData->gpttab.backupcount; t++)
                        if(strcmp(tmp, pData->gpttab.backup[t].partname) == 0) {
                            retval = 1;
                            printf("partition[%s] backup flag!\n", pData->gpttab.backup[t].partname);
                            if (pData->gpttab.backup[t].needrecovery == 1)
                                continue;
                            pData->gpttab.backup[t].backupflag = 1;
                        }
                    }
                    break;
                }
            }
        }

        j = 0;
        while (pData->gpttab.deletepart[j] != NULL) {
            if (strcmp(buffer, pData->gpttab.deletepart[j]) == 0) {
                for(k = i + 1; k < pData->numParts; k++) {
                    char16tochar(pData->partitions[k].name, tmp);
                    for(t = 0; t < pData->gpttab.backupcount; t++)
                        if(strcmp(tmp, pData->gpttab.backup[t].partname) == 0) {
                            printf("partition[%s] backup flag!\n", pData->gpttab.backup[t].partname);
                            retval = 1;
                    }
                }
            }
            j++;
        }

        for(j = 0; j < pData->gpttab.newpartcount; j++) {
            if(strcmp(buffer, pData->gpttab.newpart[j].partbehind) == 0) {
                for(k = i + 1; k < pData->numParts; k++) {
                    char16tochar(pData->partitions[k].name, tmp);
                    for(t = 0; t < pData->gpttab.backupcount; t++) {
                        if(strcmp(tmp, pData->gpttab.backup[t].partname) == 0) {
                            retval = 1;
                            printf("partition[%s] backup flag!\n", pData->gpttab.backup[t].partname);
                            if (pData->gpttab.backup[t].needrecovery == 1) {
                                continue;
                            }
                            pData->gpttab.backup[t].backupflag = 1;
                        }
                    }
                }
            }
        }
    }
    return retval;
}

static int CheckExistBackup(GPTData *pData)
{
    uint32_t  i, ret;
    char buf[36];
    char filepath[256]={0};
    int dirlen,retval = 0;

    dirlen = strlen(pData->backup_dir);
    if (pData->backup_dir[dirlen -1] != '/') {
        pData->backup_dir[dirlen] = '/';
        pData->backup_dir[dirlen +1] = 0;
    }
    for(i = 0; i < pData->gpttab.backupcount; i++) {
        strcpy(filepath, pData->backup_dir);
        sprintf(buf, ".bak.%s.img", pData->gpttab.backup[i].partname);
        printf("CheckExistBackup :: buf :%s\n", buf);
        strcat(filepath, buf);
        printf("BackupPartition:: final filepath =%s\n", filepath);
        ret = access(filepath, F_OK);
        if(ret == 0) {
            printf("access retval == 0\n");
            pData->gpttab.backup[i].needrecovery = 1;
            pData->gpttab.backup[i].backupflag= 0;
            retval = 1;
        }
    }

    return retval;
}

int BackupPartData2File(GPTData *pData)
{
    uint32_t i;
    uint32_t  j;
    char buffer[36];
    int retval = 1;
    int exist_backup;

    exist_backup = CheckExistBackup(pData); //check if already have backup in sdcard, if yes, mean we only recovery them.
    if(exist_backup == 1) {
        printf("Backup has existed!\n");
        pData->needBackup = 1;
    }

    pData->needBackup |= BackupCheck(pData); //check if some partitioins will be changed, if so ,we shall back up them first.
                                             // this is what we will do below.
    if(pData->needBackup == 0) {
        printf("BackupPartData2File:: GPT partition table will not change, don't need  backup!\n");
        return 1;
    }

    printf("BackupPartData2File:: entry!\n");
    for(i = 0; i < pData->numParts; i++) {
        char16tochar(pData->partitions[i].name, buffer);
        for(j = 0; j < pData->gpttab.backupcount; j++) {
            if(strcmp(buffer, pData->gpttab.backup[j].partname) == 0) {
                if (pData->gpttab.backup[j].backupflag == 1) {
                    printf("backuppartdata2File:: backup %s part.\n", buffer);
                    retval = BackupPartition(pData,i);
                    if(retval == -1) {
                        printf("backup partition data failed! \n");
                        return 0;
                    }
                    else {
                        pData->gpttab.backup[j].needrecovery = 1;
                        printf("BackupPartData2File:: Recovery flay = 1\n");
                    }
                }
                else {
                    printf("backupPartdata2FIle:: partition %s need not backup!\n", pData->gpttab.backup[j].partname);
                }
            }
        }
    }
    return 1;
}


#if 0
int IsFreePartNum(uint32_t partNum) {
    return ((partNum < numParts) && (partitions != NULL) && (!partitions[partNum].IsUsed()));
}
#endif

void chartochar16(char *partname, uint16_t *buffer)
{
    uint32_t i;
    for(i = 0; i < strlen(partname); i++) {
        buffer[i] = partname[i];
    }
}



int CreateLargestPart(GPTData *pData, int partNum, int tabNum, uint64_t startSector, uint64_t endSector)
{
    int retval = 1; // assume there'll be no problems
    uint16_t buffer[36];
    memset(buffer, 0, 36);

    GPTPart * parts ;

    if (startSector < endSector) {
        parts = malloc(sizeof(GPTPart) * (pData->numParts + 1));
        memset(parts, 0, sizeof(GPTPart) * (pData->numParts + 1));
        memcpy(parts, pData->partitions, sizeof(GPTPart) * pData->numParts);

        free(pData->partitions);
        pData->partitions = parts;

        int i = pData->numParts;
        while (i > partNum) {
            pData->partitions[i] = pData->partitions[i - 1];
            i--;
        }

        printf("CreateLargePart: blk_device %s\n", pData->gpttab.newpart[tabNum].partname);
        chartochar16(pData->gpttab.newpart[tabNum].partname, buffer);

        memcpy(parts[partNum + 1].PartType, parts[partNum].PartType, 16) ;
        memcpy(parts[partNum + 1].GUIDData, parts[partNum].GUIDData, 16) ;
        parts[partNum].GUIDData[15] += 1;
        memcpy(&parts[partNum + 1].attributes, &parts[partNum].attributes, sizeof(uint64_t)) ;
        memcpy(parts[partNum + 1].name, buffer, 36);
        parts[partNum + 1].firstLBA = startSector;
        parts[partNum + 1].lastLBA = endSector;
        //parts[partNum].lastLBA = startSector - 1;
        pData->numParts = pData->numParts + 1;
        pData->mainHeader.numParts = pData->numParts;
    }
    else {
        retval = 0;
    }
    return retval;
}


int MovePartitionLBA(GPTData *pData, int partNum, long long offsetLBA)
{
    uint32_t  i;
    char buffer[36] = {0};
    char tmp[36] = {0};
    int retval = 0;

    strcpy(tmp, "userdata");
    if (pData->gpttab.resizablePart != NULL)
        strcpy(tmp, pData->gpttab.resizablePart);

    for (i = partNum + 2; i < pData->numParts; i++) {
        char16tochar(pData->partitions[i].name, buffer);
        pData->partitions[i].firstLBA  += offsetLBA;
        if (strcmp(buffer, tmp) == 0) {
            break;
        }
        pData->partitions[i].lastLBA  += offsetLBA;
    }
    return retval;
}

int CreatePartition(GPTData *pData, int optNum)
{
    uint32_t  i = 0, j;
    int retval = 1;
    char buffer[36];
    uint64_t startSector, endSector;
    long long offsetLBA;
    long long filesize;
    //check if header->partype == header->GUIDDate
#if 0

    memcpy(buffer, pData->partitions[20].PartType, 16);
    printf("CreatePartition: partitionTpye 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");

    memcpy(buffer, pData->partitions[20].GUIDData, 16);
    printf("CreatePartition: GUIDdata 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");

    memcpy(buffer, pData->partitions[21].PartType, 16);
    printf("CreatePartition: partitionTpye 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");

    memcpy(buffer, pData->partitions[21].GUIDData, 16);
    printf("CreatePartition: GUIDdata 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");
#endif

    //printf("CreatePartition: firstUsableLBA %lld\n", pData->mainHeader.firstUsableLBA);
    //printf("CreatePartition: lastUsableLBA %lld\n", pData->mainHeader.lastUsableLBA);
    //printf("CreatePartition: backupLBA %lld\n", pData->mainHeader.backupLBA);

    printf("changepartition:: partbehind [%s]\n", pData->gpttab.newpart[optNum].partbehind);
    printf("CreatePartition: image_size %lld M\n", pData->gpttab.newpart[optNum].partsize);
    filesize = pData->gpttab.newpart[optNum].partsize ;

    offsetLBA = filesize * 1024 * 2;
    printf("CreatePartition: offsetLBA %lld\n", offsetLBA);

    if(offsetLBA <= 0) {
        printf("CreatePartition: image_size error!\n");
        return 0;
    }

    if (pData->partitions != NULL) {
        //while ((i < pData->numParts) && pData->partitions[i].partitionType
        while (i < pData->numParts) {
            char16tochar(pData->partitions[i].name, buffer);
            if(strcmp(buffer, pData->gpttab.newpart[optNum].partbehind) == 0) {
                break;
            }
            i++;
        }
        if (i >= pData->numParts) {
            printf("CreatePartition:: add a new partition, but partbehind option not pointed to a partition, or not found!\n");
            return 0;
        }

        printf("CreatePartition: behindpart part: %s\n", pData->gpttab.newpart[optNum].partbehind);
        printf("CreatePartition: %s firstLBA %lld\n", pData->gpttab.newpart[optNum].partbehind,pData->partitions[i].firstLBA);
        printf("CreatePartition: %s lastLBA %lld\n", pData->gpttab.newpart[optNum].partbehind,pData->partitions[i].lastLBA);
        startSector = pData->partitions[i].lastLBA  + 1;
        endSector = pData->partitions[i].lastLBA + offsetLBA;
        retval = CreateLargestPart(pData, i, optNum, startSector, endSector);
        if(retval == 0) {
            printf("CreateLagrestPart fail!\n");
            return 0;
        }

        retval = MovePartitionLBA(pData, i , offsetLBA);

    }
    else {
        printf("partitions table is empty!\n");
        return 0;
    }

    memcpy(buffer, pData->partitions[i].PartType, 16);
    printf("CreatePartition: partitionTpye 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");

    memcpy(buffer, pData->partitions[i].GUIDData, 16);
    printf("CreatePartition: GUIDdata 0x");
    for(j = 0; j < 16; j++) {
        printf("%x", buffer[j]);
    }
    printf("\n");
    return 1;
}

int AddNewPartition(GPTData *pData)
{
    uint32_t i;
    uint32_t j;
    char buffer[36];
    int retval = 1;

    printf("AddNumPartition:: entry!\n");

    for(j = 0; j < pData->gpttab.newpartcount; j++) {
        for(i = 0; i < pData->numParts; i++) {
            char16tochar(pData->partitions[i].name, buffer);
            if(strcmp(buffer, pData->gpttab.newpart[j].partname) == 0) {
                printf("this %s partition has exited, can't add this partition\n", buffer);
                break;
            }
        }
        if (i < pData->numParts) {
            continue;
        }
        printf("AddNewPartition:: add %s \n", pData->gpttab.newpart[j].partname);
        retval = CreatePartition(pData, j);
        if(retval == 0) {
            printf("add new partition failed ! \n");
            return 0;
        }
        pData->addNewPart = 1;
    }
    return 1;
}

int DeletePartition(GPTData *pData)
{
    uint32_t i;
    uint32_t j;
    uint32_t z;
    char buffer[36];
    printf("DeletePartition:: entry!\n");

    for(i = 0; i< pData->numParts; i++) {
        char16tochar(pData->partitions[i].name, buffer);
        for(j = 0; j < pData->gpttab.delpartcount; j++) {
            if(strcmp(pData->gpttab.deletepart[j], buffer) == 0) {
                if(strcmp(buffer,"internalsd") == 0) {
                    printf("find internalsd and delete internalsd\n");
                    pData->partitions[i-1].lastLBA  = pData->partitions[i].lastLBA;
                    for(z = i; z < pData->numParts - 1; z++)
                        pData->partitions[z] = pData->partitions[z+1];
                    pData->numParts = pData->numParts - 1;
                    pData->mainHeader.numParts = pData->numParts;
                    return 1;
                }
            }
        }
    }
    if (i == pData->numParts)
        printf("don't find partition which should be deleted\n");
    return 0;
}

#if 0
int IsChangePartition(GPTData *pData, char *name)
{
    int i;
    int j;
    int ret;
    char buffer[36];

    printf("IsChangePartition enter!\n");

    ret = load_partition_table(pData, name);
    if(ret != SUCCESS) {
        return 0;
    }
    printf("IsChangePartition :: pData->numParts = %d, pData->count = %d\n", pData->numParts, pData->count);

#if 0
    for(i = 0; i< pData->numParts; i++)
    {
        char16tochar(pData->partitions[i].name, buffer);
        for(j = 0; j < pData->count; j++)
        {
            if(strcmp(buffer, pData->gpttab[j].blk_device) == 0)
            {
                printf("IsChangePartition :: blk_device = %s\n", pData->gpttab[j].blk_device);
                if(pData->gpttab[j].image_size > pData->partitionSize[i])
                {
                    printf("fatab 's blocksize > GPTtab 's blocksize\n");
                    ret =1;
                }
            }
        }
    }
#endif

    return SUCCESS;
}

int load_partition_table(GPTData *pData, char *name)
{
    int i;

    printf("load_partition_table enter!\n");

    FILE *partab_file;
    int cnt;
    int entries;
    int len;
    char line[256] = {0};
    const char *delim = " \t";
    char *save_ptr;
    char *p;
    GPTtab *partab;

    partab_file = fopen(name, "r");
    if(!partab_file)
    {
        printf("Cannot open file %s %s\n", name, strerror(errno));
        return FAILER;
    }

    entries = 0;

    while(par_getline(line, sizeof(line), partab_file))
    {
        /* if the last character is a newline, shorten the string by 1 byte */
        len = strlen(line);
        if(line[len - 1] == '\n')
        {
            line[len - 1] = '\0';
        }
        /* Skip any leading whitespace */
        p = line;
        while(isspace(*p))
        {
            p++;
        }
        /* ignore comments or empty lines */
        if(*p == '#' || *p == '\0')
        {
            continue;
        }
        entries++;
    }

    if(!entries)
    {
        printf("No entries found in fstab\n");
        return FAILER;
    }

    printf("load_partition_table :: entries = %d\n", entries);

    /* Allocate and init the partab structure */
    partab = (GPTtab *)malloc(sizeof(GPTtab) * entries);

    fseek(partab_file, 0, SEEK_SET);

    cnt = 0;

    while(par_getline(line, sizeof(line), partab_file))
    {
        /* if the last character is a newline, shorten the string by 1 byte */
        len = strlen(line);
        if(line[len - 1] == '\n')
        {
            line[len - 1] = '\0';
        }

        /* Skip any leading whitespace */
        p = line;
        while(isspace(*p))
        {
            p++;
        }
        /* ignore comments or empty lines */
        if(*p == '#' || *p == '\0')
        {
            continue;
        }

        /* If a non-comment entry is greater than the size we allocated, give an
         * error and quit.  This can happen in the unlikely case the file changes
         * between the two reads.
         */
        if(cnt >= entries)
        {
            printf("Tried to process more entries than counted\n");
            break;
        }

        if(!(p = strtok_r(line, delim, &save_ptr)))
        {
            printf("Error parsing blk_device\n");
            return FAILER;
        }
        partab[cnt].blk_device = strdup(p);

        if(!(p = strtok_r(NULL, delim, &save_ptr)))
        {
            printf("Error parsing image size\n");
            return FAILER;
        }
        partab[cnt].image_size = strdup(p);

        if(!(p = strtok_r(NULL, delim, &save_ptr)))
        {
            printf("Error parsing backup\n");
            return FAILER;
        }
        partab[cnt].backup = strdup(p);
        cnt++;
    }

    fclose(partab_file);

    for(i = 0; i < cnt; i++)
    {
        printf("dev = %s, size = %s, backup = %s\n", partab[i].blk_device, partab[i].image_size, partab[i].backup);
    }

    pData->gpttab = (GPTtab *)malloc(sizeof(GPTtab) * cnt);
    memcpy(pData->gpttab, partab, sizeof(GPTtab) * cnt);
    pData->count = cnt;

    for(i = 0; i < pData->count; i++)
    {
        printf("pData->count = %d, dev = %s, size = %s, backup = %s\n", pData->count,
                pData->gpttab[i].blk_device, pData->gpttab[i].image_size, pData->gpttab[i].backup);
    }

    return SUCCESS;
}
#endif

char *par_getline(char *buf, int size, FILE *file)
{
    int cnt = 0;
    int eof = 0;
    int eol = 0;
    int c;

    if (size < 1) {
        return NULL;
    }

    while (cnt < (size - 1)) {
        c = getc(file);
        if (c == EOF) {
            eof = 1;
            break;
        }

        *(buf + cnt) = c;
        cnt++;

        if (c == '\n') {
            eol = 1;
            break;
        }
    }

    /* Null terminate what we've read */
    *(buf + cnt) = '\0';

    if (eof) {
        if (cnt) {
            return buf;
        }
        else {
            return NULL;
        }
    }
    else if (eol) {
        return buf;
    }
    else {
        /* The line is too long.  Read till a newline or EOF.
         * If EOF, return null, if newline, return an empty buffer.
         */
        while(1) {
            c = getc(file);
            if (c == EOF) {
                return NULL;
            }
            else if (c == '\n') {
                *buf = '\0';
                return buf;
            }
        }
    }
}


int SaveGPTData(GPTData *pData)
{
    int allOK = 1;

    printf("SaveGPTData enter!\n");

    RecomputeCRCs(pData);

    // As per UEFI specs, write the secondary table and GPT first....
    //allOK = SavePartitionTable(pData, pData->fd, pData->secondHeader.partitionEntriesLBA);

    // Now write the secondary GPT header...
    //allOK = allOK && SaveHeader(&(pData->secondHeader), pData->fd, pData->mainHeader.backupLBA);

    // Now write the main partition tables...
    allOK = allOK && SavePartitionTable(pData, pData->fd, pData->mainHeader.partitionEntriesLBA);

    // Now write the main GPT header...
    allOK = allOK && SaveHeader(&(pData->mainHeader), pData->fd, 1);

    // To top it off, write the protective MBR...
    //allOK = allOK && protectiveMBR.WriteMBRData(&myDisk);

    DiskSync(pData->fd);

    //Close(pData->fd);

    return allOK;
}

void Close(int fd)
{
    printf("Close enter!\n");

    if(close(fd) < 0)
    {
        printf("Close device error : %s", strerror(errno));
    }
}


int DiskSync(int fd)
{
    int i;
    int ret = 0;

    printf("DiskSync enter!\n");

    sync();
    sleep(1); // Theoretically unnecessary, but ioctl() fails sometimes if omitted....
    fsync(fd);

    i = ioctl(fd, BLKRRPART);
    if(i < 0)
    {
        printf("Warning: The kernel is still using the old partition table. The new table will be used at the next reboot.\n");
    }
    else
    {
        ret = 1;
    }

    sync();
    sleep(1); // Theoretically unnecessary, but ioctl() fails sometimes if omitted....
    fsync(fd);

    return ret;
}

int SaveHeader(GPTHeader *header, int fd, uint64_t sector)
{
    int allOK = 1;

    printf("SaveHeader enter!\n");

    if(Seek(sector, fd))
    {
        printf("SaveHeader :: seek ok!\n");
        if(Write(header, 512, fd) == -1)
        {
            allOK = 0;
            printf("SaveHeader :: Write failer!\n");
        }
    }
    else
    {
        allOK = 0;
        printf("SaveHeader :: seek failer!\n");
    }

    return allOK;
}


int SavePartitionTable(GPTData *pData, int fd, uint64_t sector)
{
    int allOK = 1;

    printf("SavePartitionTable enter!\n");

    if(Seek(sector, fd))
    {
        printf("SavePartitionTable :: seek ok!\n");
        if(Write(pData->partitions, pData->mainHeader.sizeOfPartitionEntries * pData->numParts, fd) == -1)
        {
            printf("SavePartitionTable :: write failer!\n");
            allOK = 0;
        }
    }
    else
    {
        allOK = 0;
        printf("SavePartitionTable :: seek failer!\n");
    }

    return allOK;
}

int Write(void* buffer, int numBytes, int fd)
{
    int i;
    int numBlocks;
    char* tempSpace;
    int ret = 0;
    int blockSize = 512;

    blockSize = GetBlockSize(fd);
    if(numBytes <= blockSize)
    {
        numBlocks = 1;
        tempSpace = (char *)malloc(sizeof(char) * blockSize);
    }
    else
    {
        numBlocks = numBytes / blockSize;
        if((numBytes % blockSize) != 0)
        {
            numBlocks++;
        }
        tempSpace = (char *)malloc(sizeof(char) * numBlocks * blockSize);
    }

    memcpy(tempSpace, buffer, numBytes);

    for(i = numBytes; i < numBlocks * blockSize; i++)
    {
        tempSpace[i] = 0;
    }

    ret = write(fd, tempSpace, numBlocks * blockSize);
    if(ret < 0) {
        perror("write error:");
    }

    // Adjust the return value, if necessary....
    if(((numBlocks * blockSize) != numBytes) && (ret > 0))
    {
        ret = numBytes;
    }

    return ret;
}

int Read(void* buffer, int numBytes, int fd)
{
    int blockSize;
    int numBlocks;
    char* tempSpace;
    int ret = SUCCESS;

    printf("Read enter!\n");

    blockSize = GetBlockSize(fd);
    if(numBytes <= blockSize)
    {
        numBlocks = 1;
        printf("Read :: numBlocks = 1\n");
        tempSpace = (char* )malloc(blockSize);
    }
    else
    {
        numBlocks = numBytes / blockSize;
        if((numBytes % blockSize) != 0)
        {
            numBlocks++;
        }
        tempSpace = (char *)malloc(numBlocks * blockSize);
    }

    if(tempSpace == NULL)
    {
         printf("Unable to allocate memory in Read()!\n");
         return FAILER;
    }

    // Read the data into temporary space, then copy it to buffer
    ret = read(fd, tempSpace, numBlocks * blockSize);
    memcpy(buffer, tempSpace, numBytes);

    // Adjust the return value, if necessary....
    if(((numBlocks * blockSize) != numBytes) && (ret > 0))
    {
        ret = numBytes;
    }

    free(tempSpace);
    tempSpace = NULL;

    return ret;
}



void RecomputeCRCs(GPTData *pData)
{
    uint32_t crc;
    uint32_t hSize;

    printf("RecomputeCRCs enter!\n");

    if(pData->mainHeader.headerSize > sizeof(pData->mainHeader))
    {
        hSize = pData->secondHeader.headerSize = pData->mainHeader.headerSize = HEADER_SIZE;
    }
    else
    {
        hSize = pData->secondHeader.headerSize = pData->mainHeader.headerSize;
    }

    // Compute CRC of partition tables & store in main and secondary headers
    crc = chksum_crc32((unsigned char*)pData->partitions, pData->numParts * GPT_SIZE);
    pData->mainHeader.partitionEntriesCRC = crc;
    pData->secondHeader.partitionEntriesCRC = crc;

    pData->mainHeader.headerCRC = 0;
    pData->secondHeader.headerCRC = 0;
    crc = chksum_crc32((unsigned char*)&(pData->mainHeader), hSize);
    pData->mainHeader.headerCRC = crc;
    crc = chksum_crc32((unsigned char*)&(pData->secondHeader), hSize);
    pData->secondHeader.headerCRC = crc;

    printf("RecomputeCRCs :: partitionEntriesCRC = %d, pData->mainHeader.headerCRC = %d, pData->secondHeader.headerCRC = %d\n",
              pData->mainHeader.partitionEntriesCRC, pData->mainHeader.headerCRC, pData->secondHeader.headerCRC);

    return;
}

void DisplayGPTData(GPTData *pData)
{
    uint32_t i;
    int j;

    printf("DisplayGPTData enter!\n");

    pData->partitionSize = (uint64_t *)malloc(sizeof(uint64_t) * pData->numParts);

    for(i = 0; i < pData->numParts; i++)
    {
        printf("pData->partitions[%d].firstLBA = %lld\n", i, pData->partitions[i].firstLBA);
        printf("pData->partitions[%d].lastLBA = %lld\n", i, pData->partitions[i].lastLBA);
        //printf("pData->partitions[%d].name = %s\n", i, pData->partitions[i].name);
        //size = (last-first+1)*sector;
        for(j = 0; j < 36, pData->partitions[i].name[j] != 0; j++)
        {
            printf("%c",pData->partitions[i].name[j]);
        }
        printf("     ");
        pData->partitionSize[i] = (pData->partitions[i].lastLBA - pData->partitions[i].firstLBA + 1) * GetBlockSize(pData->fd);
        printf("pData->partitionSize[%d] = %lld     ", i, pData->partitionSize[i]);
        printf("%lldM", pData->partitionSize[i] / (1024 * 1024));
        printf("\n");
        // printf("%lld   \n",pData->partitions[i].attributes);
    }
}



int LoadPartitionTable(GPTData *pData, GPTHeader *header, int fd)
{
    int ret;
    int sizeOfParts;
    uint32_t newCRC;

    printf("LoadPartitionTable enter! header->partitionEntriesLBA = %lld\n", header->partitionEntriesLBA);

    ret = Seek(header->partitionEntriesLBA, fd);
    //if (retval == 1)
    //  retval = SetGPTSize(header.numParts, 0);
    if(ret == 1)
    {
        sizeOfParts = header->numParts * header->sizeOfPartitionEntries;
        printf("LoadPartitionTable :: header->numParts = %d, header->sizeOfPartitionEntries = %d\n",
            header->numParts, header->sizeOfPartitionEntries);

        if(Read(pData->partitions, sizeOfParts, fd) != sizeOfParts)
        {
            printf("Warning! Read error, Misbehavior now likely!\n");
            ret = 0;
        }
        newCRC = chksum_crc32((unsigned char*)pData->partitions, sizeOfParts);
        printf("LoadPartitionTable :: newCRC = %d, header->partitionEntriesCRC = %d\n", newCRC, header->partitionEntriesCRC);
        pData->mainPartsCrcOk = pData->secondPartsCrcOk = (newCRC == header->partitionEntriesCRC);
        printf("LoadPartitionTable :: partition crc is %d\n", pData->mainPartsCrcOk);
        //if (IsLittleEndian() == 0)
        //    ReversePartitionBytes();
        if (!pData->mainPartsCrcOk)
        {
            printf("Caution! After loading partitions, the CRC doesn't check out!\n");
        }
    }
    return ret;
}

void RebuildSecondHeader(GPTData *pData)
{
    pData->secondHeader.signature = GPT_SIGNATURE;
    pData->secondHeader.revision = pData->mainHeader.revision;
    pData->secondHeader.headerSize = pData->mainHeader.headerSize;
    pData->secondHeader.headerCRC = 0;
    pData->secondHeader.reserved = pData->mainHeader.reserved;
    pData->secondHeader.currentLBA = pData->mainHeader.backupLBA;
    pData->secondHeader.backupLBA = pData->mainHeader.currentLBA;
    pData->secondHeader.firstUsableLBA = pData->mainHeader.firstUsableLBA;
    pData->secondHeader.lastUsableLBA = pData->mainHeader.lastUsableLBA;
    //pData->secondHeader.diskGUID = pData->mainHeader.diskGUID;
    pData->secondHeader.partitionEntriesLBA = pData->secondHeader.lastUsableLBA + 1;
    pData->secondHeader.numParts = pData->mainHeader.numParts;
    pData->secondHeader.sizeOfPartitionEntries = pData->mainHeader.sizeOfPartitionEntries;
    pData->secondHeader.partitionEntriesCRC = pData->mainHeader.partitionEntriesCRC;
    memcpy(pData->secondHeader.reserved2, pData->mainHeader.reserved2, sizeof(pData->secondHeader.reserved2));
    pData->secondCrcOk = pData->mainCrcOk;
    //SetGPTSize(pData->secondHeader.numParts, 0);
}

void RebuildMainHeader(GPTData *pData)
{
    pData->mainHeader.signature = GPT_SIGNATURE;
    pData->mainHeader.revision = pData->secondHeader.revision;
    pData->mainHeader.headerSize = pData->secondHeader.headerSize;
    pData->mainHeader.headerCRC = 0;
    pData->mainHeader.reserved = pData->secondHeader.reserved;
    pData->mainHeader.currentLBA = pData->secondHeader.backupLBA;
    pData->mainHeader.backupLBA = pData->secondHeader.currentLBA;
    pData->mainHeader.firstUsableLBA = pData->secondHeader.firstUsableLBA;
    pData->mainHeader.lastUsableLBA = pData->secondHeader.lastUsableLBA;
    //pData->mainHeader.diskGUID = pData->secondHeader.diskGUID;
    pData->mainHeader.partitionEntriesLBA = 2;
    pData->mainHeader.numParts = pData->secondHeader.numParts;
    pData->mainHeader.sizeOfPartitionEntries = pData->secondHeader.sizeOfPartitionEntries;
    pData->mainHeader.partitionEntriesCRC = pData->secondHeader.partitionEntriesCRC;
    memcpy(pData->mainHeader.reserved2, pData->secondHeader.reserved2, sizeof(pData->mainHeader.reserved2));
    pData->mainCrcOk = pData->secondCrcOk;
    //SetGPTSize(pData->mainHeader.numParts, 0);
}

int CheckHeaderValidity(GPTData *pData)
{
    int valid = 3;

    printf("pData->mainHeader.signature = %x\n", pData->mainHeader.signature);
    printf("pData->mainHeader.revision = %x", pData->mainHeader.revision);
    printf("pData->secondHeader.signature = %x\n", pData->secondHeader.signature);
    printf("pData->secondHeader.revision = %x", pData->secondHeader.revision);

    if((pData->mainHeader.signature != GPT_SIGNATURE) || (!CheckHeaderCRC(&(pData->mainHeader), pData->fd)))
    {
        valid -= 1;
        printf("CheckHeaderValidity :: check main header crc failer!\n");
    }
    else if(((pData->mainHeader).revision != 0x00010000) && valid)
    {
        valid -= 1;
        printf("CheckHeaderValidity :: Unsupported GPT version in main header");
    }

    if((pData->secondHeader.signature != GPT_SIGNATURE) || (!CheckHeaderCRC(&(pData->secondHeader), pData->fd)))
    {
        valid -= 2;
        printf("CheckHeaderValidity :: check second header crc failer!\n");
    }
    else if((pData->secondHeader.revision != 0x00010000) && valid)
    {
        valid -= 2;
        printf("CheckHeaderValidity :: Unsupported GPT version in second header");
    }

    printf("CheckHeaderValidity :: valid = %d\n", valid);

    return valid;
}

int LoadHeader(GPTData *pData, GPTHeader *header, int fd, uint64_t sector, int *crcOk)
{
    int allOK = 1;
    GPTHeader tempHeader;

    Seek(sector, fd);
    if(Read(&tempHeader, 512, fd) != 512)
    {
      printf("Warning! Read error; strange behavior now likely!\n");
      allOK = 0;
    }

    // Reverse byte order, if necessary
    //if (IsLittleEndian() == 0) {
    //  ReverseHeaderBytes(&tempHeader);
    //}

    *crcOk = CheckHeaderCRC(&tempHeader, fd);
    printf("LoadHeader :: crcOk = %d, tempHeader.numParts = %d\n", *crcOk, tempHeader.numParts);

    if(allOK && (pData->numParts != tempHeader.numParts) && *crcOk)
    {
        printf("LoadHeader :: SetGPTSize\n");
        allOK = SetGPTSize(pData, tempHeader.numParts, 0);
    }

    *header = tempHeader;
    return allOK;
}

int SetGPTSize(GPTData *pData, uint32_t numEntries, int fillGPTSectors)
{
    int allOK = 1;
    GPTPart* newParts;
    uint32_t entriesPerSector;

    printf("SetGPTSize enter!\n");

    // First, adjust numEntries upward, if necessary, to get a number
    // that fills the allocated sectors
    entriesPerSector = pData->blockSize / GPT_SIZE;
    if(fillGPTSectors && ((numEntries % entriesPerSector) != 0))
    {
      printf("Adjusting GPT size\n");
      numEntries = ((numEntries / entriesPerSector) + 1) * entriesPerSector;
    }

    if(((numEntries != pData->numParts) || (pData->partitions == NULL)) && (numEntries > 0))
    {
        printf("SetGPTSize :: malloc memory for GPTPart!\n");

        newParts = (GPTPart *)malloc(sizeof(GPTPart) * numEntries);
        if(NULL != newParts)
        {
            pData->partitions = newParts;
        }
        pData->numParts = numEntries;
        pData->mainHeader.firstUsableLBA = ((numEntries * GPT_SIZE) / pData->blockSize) +
                                  (((numEntries * GPT_SIZE) % pData->blockSize) != 0) + 2 ;
        pData->secondHeader.firstUsableLBA = pData->mainHeader.firstUsableLBA;
        MoveSecondHeaderToEnd(pData);
    }
    pData->mainHeader.numParts = pData->numParts;
    pData->secondHeader.numParts = pData->numParts;

    printf("SetGPTSize :: pData->mainHeader.numParts = %d\n", pData->mainHeader.numParts);

    return allOK;
}

void MoveSecondHeaderToEnd(GPTData *pData)
{
    printf("MoveSecondHeaderToEnd enter!\n");

    pData->mainHeader.backupLBA = pData->secondHeader.currentLBA = pData->diskSize - 1;
    pData->mainHeader.lastUsableLBA = pData->secondHeader.lastUsableLBA = pData->diskSize - pData->mainHeader.firstUsableLBA;
    pData->secondHeader.partitionEntriesLBA = pData->secondHeader.lastUsableLBA + 1;
}

int CheckHeaderCRC(GPTHeader* header, int fd)
{
    uint32_t oldCRC;
    uint32_t newCRC;
    int hSize;
    uint8_t *temp;

    printf("CheckHeaderCRC enter!\n");

    // Back up old header CRC and then blank it, since it must be 0 for
    // computation to be valid
    oldCRC = header->headerCRC;
    header->headerCRC = 0;

    hSize = header->headerSize;

    printf("CheckHeaderCRC :: hSize = %d\n", hSize);

    //if (IsLittleEndian() == 0)
    //  ReverseHeaderBytes(header);

    if((hSize > GetBlockSize(fd)) || (hSize < HEADER_SIZE))
    {
        hSize = HEADER_SIZE;
        printf("Warning! Header size is invalid. Setting the header size for CRC computation to HEADER_SIZE\n");
    }
    else if((hSize > sizeof(GPTHeader)))
    {
        printf("Caution! Header size for CRC check is greater than sizeof(GPTHeader)\n");
    }

    printf("CheckHeaderCRC :: hSize = %d\n", hSize);

    temp = (uint8_t *)malloc(hSize);
    memset(temp, 0, hSize);
    if(hSize < sizeof(GPTHeader))
    {
        memcpy(temp, header, hSize);
    }
    else
    {
        memcpy(temp, header, sizeof(GPTHeader));
    }

    newCRC = chksum_crc32((unsigned char*)temp, hSize);
    free(temp);
    temp = NULL;

    //if (IsLittleEndian() == 0)
    //  ReverseHeaderBytes(header);

    header->headerCRC = oldCRC;
    printf("oldCRC = %d, newCRC = %d\n", oldCRC, newCRC);

    return (oldCRC == newCRC);
}

static int RecoveryAPartition(GPTData *pData, int tabnum, int partnum)
{
    int i ,ret = 1;
    int fd;
    long long partsize;
    long long filesize;
    int readed, writed;
    char file[100];
    char filepath[256];
    char tmp[4096];
    struct stat	 filestat;

    printf("\nRecoveryAPartition::entry\n");

    strcpy(filepath, pData->backup_dir);
    printf("RecoveryAPartition::file path:%s\n", filepath);
    sprintf(file, ".bak.%s.img", pData->gpttab.backup[tabnum].partname);
    printf("RecoveryAPartition::file:%s\n", file);
    strcat(filepath, file);

    printf("RecoveryAPartition:: filepath  %s!\n", filepath);

    partsize = pData->blockSize* (pData->partitions[partnum].lastLBA - pData->partitions[partnum].firstLBA + 1);
    printf("RecoveryAPartition:: partsize %lld \n", partsize);

    fd = open(filepath, O_RDONLY);
    if(fd < 0) {
        perror("RecoveryAPartition::");
        return -1;
    }

    ret = fstat(fd, &filestat);
    if(ret < 0) {
        perror("fstat::");
        return -1;
    }
    filesize = filestat.st_size;
    printf("RecoveryAPartition::filesize is %lld in sdcard\n", filesize);
    if(filesize > partsize) {
        printf("RecoveryAPartition::filesize > partsize!\n");
        return -1;
    }

    Seek(pData->partitions[partnum].firstLBA, pData->fd);

    int  readlen;
    while(filesize > 0) {
        if(filesize < 4096) {
            readlen = filesize;
        }
        else {
            readlen = 4096;
        }
        readed = read(fd, tmp, readlen);
        if((readed < 0) || (readed != readlen)){
            printf("Backuppartition:: can't read, error = %s\n", strerror(errno));
            return -1;
        }
        writed = write(pData->fd, tmp, readed);
        if((writed < 0) || (readed != writed)) {
            printf("Backuppartition:: can't write, error = %s\n", strerror(errno));
            return -1;
        }
        filesize -= 4096;
    }

    SaveGPTData(pData);

    uint64_t t = 1;  //if this partition data have been recoveryed to GPT, clear the flag.
    printf("RecoveryAPartition :: partition[%s]->artributes %lld\n", file , pData->partitions[partnum].attributes);
    pData->partitions[partnum].attributes &= ~(t << BACKUP_FLAG);
    printf("RecoveryAPartition :: partition[%s]->artributes %lld\n", file , pData->partitions[partnum].attributes);

    close(fd);
    unlink(filepath);
    return 1;
}

int RecoveryPartition(GPTData *pData)
{
    uint32_t  i, j;
    int ret;
    char buffer[36];
    printf("\nRecoveryPartition:: entry!\n");
    if(pData->needBackup == 0) {
        printf("RecoveryPartition:: no GPT part be backed up, don't need recovery!\n");
        return 1;
    }
    if(NULL == pData->backup_dir) {
        printf("RecoveryPartiton::backup_dir is NULL!\n");
        return 1;
    }
    for(i = 0; i < pData->gpttab.backupcount; i++) {
        if(pData->gpttab.backup[i].needrecovery == 1) {
            for(j = 0; j < pData->numParts; j++) {
                char16tochar(pData->partitions[j].name, buffer);
                if(strcmp(buffer, pData->gpttab.backup[i].partname) == 0) {
                    ret = RecoveryAPartition(pData, i, j);
                    if(ret < 0) {
                        printf("RecoveryPartition:: recovery %s partition fail!\n", pData->gpttab.backup[i].partname);
                        return 0;
                    }
                }
            }
        }
    }
    return 1;
}

int FinalDestory(GPTData *pData)
{
    close(pData->fd);
    return 1;
}

static int ParseFileLine(GPTData *pData, FILE *fp)
{
    char *p;
    char buffer[256]={0};

    printf("ParseFileLine :: entry!\n");

    while(fgets(buffer, 256, fp) != NULL) {
        buffer[strlen(buffer) - 1] = '\0';
        p = strtok(buffer, " ");
        printf("ParseCOnfigFile:: command:%s\n", p);

        if (strcmp(p, "modify_part_size") == 0) {
            pData->gpttab.changesizecount++;
        }
        else if (strcmp(p, "modify_part_name") == 0) {
            pData->gpttab.changenamecount++;
        }
        else if (strcmp(p, "new_part") == 0) {
            pData->gpttab.newpartcount++;
        }
        else if (strcmp(p, "important_part") == 0) {
            pData->gpttab.backupcount++;
        }
        else if (strcmp(p, "delete_part") == 0) {
            pData->gpttab.delpartcount++;
        }
    }

    if(pData->gpttab.changesizecount != 0) {
        pData->gpttab.changepartsize = malloc(sizeof(ChangePartsize) * pData->gpttab.changesizecount);
        memset(pData->gpttab.changepartsize, 0, pData->gpttab.changesizecount);
        if (pData->gpttab.changepartsize == NULL) {
            printf("malloc failed!\n");
            perror("changesize:");
            return 0;
        }
    }
    if(pData->gpttab.changenamecount != 0) {
        pData->gpttab.changepartname= malloc(sizeof(ChangePartname) * pData->gpttab.changenamecount);
        memset(pData->gpttab.changepartname, 0, sizeof(ChangePartname) * pData->gpttab.changenamecount);
        if (pData->gpttab.changepartname == NULL) {
            printf("malloc failed!\n");
            perror("changename:");
            return 0;
        }
    }
    if(pData->gpttab.newpartcount != 0) {
        pData->gpttab.newpart= malloc(sizeof(CreateNewPart) * pData->gpttab.newpartcount);
        memset(pData->gpttab.newpart, 0, sizeof(CreateNewPart) * pData->gpttab.newpartcount);
        if (pData->gpttab.newpart== NULL) {
            printf("malloc failed!\n");
            printf("newpart");
            return 0;
        }
    }
    if(pData->gpttab.backupcount != 0) {
        pData->gpttab.backup= malloc(sizeof(BackupPart) * pData->gpttab.backupcount);
        memset(pData->gpttab.backup, 0, sizeof(BackupPart) * pData->gpttab.backupcount);
        if (pData->gpttab.backup== NULL) {
            printf("malloc failed!\n");
            perror("backup");
            return 0;
        }
    }

    printf("ParseFileLine:: changesize:%d, changename:%d, newPart:%d, backuppart:%d\n", pData->gpttab.changesizecount,\
            pData->gpttab.changenamecount, pData->gpttab.newpartcount, pData->gpttab.backupcount);
    return 1;
}

int ParseConfigFile(GPTData *pData, char *cfg_name)
{
    printf("ParseConfigFile : entry!\n");

    int i, j;
    uint32_t  m,n,q,t, r;
    int ret;
    FILE *fp;
    char *p;
    char buffer[256] = {0};

    fp = fopen(cfg_name, "r");
    if(!fp)
    {
        printf("Cannot open file %s %s\n", cfg_name, strerror(errno));
        return FAILER;
    }

    ret = ParseFileLine(pData, fp);
    if(ret == 0) {
        return 0;
    }
    fseek(fp, 0, SEEK_SET);

    m = n = q = t = r =  0;
    while(fgets(buffer, 256, fp) != NULL) {
        buffer[strlen(buffer) - 1] = '\0';
        p = strtok(buffer, " ");
        printf("ParseCOnfigFile:: command:%s\n", p);

        if (strcmp(p, "config_version") == 0) {
            p = strtok(NULL, " ");
            printf("configfile version : %s\n", p);
            if(p == NULL) {
                printf("ParseConfigFIle: error options!\n");
                return 0;
            }
        }
        else if (strcmp(p, "modify_part_size") == 0) {
            if(m < pData->gpttab.changesizecount) {
                p = strtok(NULL, " ");
                if(p == NULL) {
                    printf("ParseConfigFIle: error options!\n");
                    return 0;
                }
                strcpy(pData->gpttab.changepartsize[m].partname, p);

                p = strtok(NULL, " ");
                printf("new_size: %s\n", p);
                if(p == NULL) {
                    printf("ParseConfigFIle: error options!\n");
                    return 0;
                }
                pData->gpttab.changepartsize[m].newsize = atoll(p);
                m++;
            }
        }
        else if (strcmp(p, "modify_part_name") == 0) {
            if(n < pData->gpttab.changenamecount) {
                p = strtok(NULL, " ");
                strcpy(pData->gpttab.changepartname[n].partname, p);
                printf("part_name: %s\n", pData->gpttab.changepartname[n].partname);

                p = strtok(NULL, " ");
                strcpy(pData->gpttab.changepartname[n].newpartname, p);
                printf("new_name: %s\n", pData->gpttab.changepartname[n].newpartname);
                n++;
              }
        }
        else if (strcmp(p, "new_part") == 0) {
            if(q < pData->gpttab.newpartcount) {
                p = strtok(NULL, " ");
                strcpy(pData->gpttab.newpart[q].partname, p);
                printf("part_name: %s\n", pData->gpttab.newpart[q].partname);
                p = strtok(NULL, " ");
                strcpy(pData->gpttab.newpart[q].partbehind, p);
                printf("partbehind: %s\n", pData->gpttab.newpart[q].partbehind);

                p = strtok(NULL, " ");
                pData->gpttab.newpart[q].partsize = atoll(p);
                printf("part_size: %s\n", p);
                q++;
            }
        }
        else if (strcmp(p, "important_part") == 0) {
            if( t < pData->gpttab.backupcount) {
                p = strtok(NULL, " ");
                if(p == NULL)
                    perror("ParseConfigFile:important_part strtok:");
                strcpy(pData->gpttab.backup[t].partname, p);
                printf("part_name: %s\n", pData->gpttab.backup[t].partname);

                t++;
            }
        }
        else if (strcmp(p, "delete_part") == 0) {
            if (r < 10) {
                p = strtok(NULL, " ");
                if (p == NULL) {
                    perror("ParseConfigFile: delete_part strtok:");
                }
                pData->gpttab.deletepart[r] = malloc (strlen(p) + 1);
                strcpy(pData->gpttab.deletepart[r++], p);
                printf("part_name: %s\n", p);
            }
            else {
                printf("too many parttitions will be deleted (default not more than 10 part)!\n");
                return 0;
            }
        }
        else if (strcmp(p, "resizable_part") == 0) {
            p = strtok(NULL, " ");
            printf("part_name: %s\n", p);
            pData->gpttab.resizablePart = malloc(strlen(p) + 1);
            strcpy(pData->gpttab.resizablePart, p);
        }
        else {
            printf("invalid command line!\n");
        }
    }
    fclose(fp);
    return 1;
}

void DisplayConfigFile(GPTData * pData)
{
    uint32_t  i;

    printf("~~~~~~~~~~~~DisplayConfigFile~~~~~~~~~~~~~~\n");
    for (i = 0; i < pData->gpttab.changesizecount; i++) {
        printf("changepartsize:%s ", pData->gpttab.changepartsize[i].partname);
        printf(" %lld\n", pData->gpttab.changepartsize[i].newsize);
    }

    for (i = 0; i < pData->gpttab.changenamecount; i++) {
        printf("changepartname:%s ", pData->gpttab.changepartname[i].partname);
        printf(" %s\n", pData->gpttab.changepartname[i].newpartname);
    }

    for (i = 0; i < pData->gpttab.newpartcount; i++) {
        printf("newpart:%s ", pData->gpttab.newpart[i].partname);
        printf(" %s", pData->gpttab.newpart[i].partbehind);
        printf(" %lld\n", pData->gpttab.newpart[i].partsize);
    }

    for (i = 0; i < pData->gpttab.backupcount; i++) {
        printf("backuppart:%s ", pData->gpttab.backup[i].partname);
        printf(" %d\n", pData->gpttab.backup[i].needrecovery);
    }

    i = 0;
    printf("deletepart:");
    while (pData->gpttab.deletepart[i] != NULL) {
        printf(" %s", pData->gpttab.deletepart[i++]);
    }
    printf("\n");

    printf("resizablepart:%s\n", pData->gpttab.resizablePart);

    printf("~~~~~~~~~~~DisplayConfigFile~~~~~~~~~~~~~~~\n");
}

