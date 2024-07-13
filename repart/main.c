#include <stdio.h>
#include <unistd.h>
#include "gptdata.h"


int main(int argc, char *argv[])
{
    GPTData *mGPTData;
    char cfgfile[40] = {0};
    int ret = 1;

    printf("gpt partition enter!\n");

    dev_name = malloc(256);
    strcpy(dev_name, "/dev/block/mmcblk0");

    mGPTData = (GPTData *)malloc(sizeof(GPTData));
    if(NULL == mGPTData)
    {
        printf("malloc GPTData failer!\n");
        return 0;
    }
    memset(mGPTData, 0, sizeof(GPTData));
    InitializeGPTData(mGPTData);

    int ch;
    while ((ch = getopt(argc, argv, "b:c:d:")) != -1) {
        switch(ch) {
            case 'b':
                mGPTData->backup_dir = malloc(256);
                memset(mGPTData->backup_dir, 0, 256);
                strcpy(mGPTData->backup_dir, optarg);
                printf(" Have option -b is %s !\n", mGPTData->backup_dir);
                break;
            case 'c':
                printf(" Have option -c is %s !\n", optarg);
                strcpy(cfgfile, optarg);
                //ParseConfigFile(mGPTData, optarg);
                break;
            case 'd':
                strcpy(dev_name, optarg);
                printf(" Have option -d is %s !\n", dev_name);
                break;
            case '?':
                printf("Unknown option: %c !\n", (char)optopt);
        }
    }

    if(cfgfile == NULL) {
        printf("this tool must have -c option pointed a configfile!\n");
        return 0;
    }

    ret = LoadPartitions(mGPTData, dev_name);
    if(ret == 0) {
        printf("LoadPartitions failed!\n");
        return 0;
    }

    DisplayGPTData(mGPTData);

    // IsChangePartition(mGPTData, "partition.partab");

    ret = ParseConfigFile(mGPTData, cfgfile); //parse config file
    if (ret == 0) {
        printf("IsChangePartition parse config file error!\n");
        return ret;
    }

    DisplayConfigFile(mGPTData);

    ret = BackupPartData2File(mGPTData);
    if(ret == 0)
        return 0;

    ret = ChangePartitionSize(mGPTData);
    if(ret == 0)
        return 0;

    ret = AddNewPartition(mGPTData);

    ret = DeletePartition(mGPTData);

    DisplayGPTData(mGPTData);

    ret = SaveGPTData(mGPTData);
    if(ret == 0)
        return 0;

    ret = RecoveryPartition(mGPTData);
    if(ret == 0)
        return 0;
#if 0
    if(mGPTData->needBackup == 1) {
        ret = SaveGPTData(mGPTData);
        if(ret == 0)
        return 0;
    }
#endif

    FinalDestory(mGPTData);
    if(mGPTData->needBackup || mGPTData->addNewPart)  //GPT have been changed
        return 2;

    return SUCCESS;
}

