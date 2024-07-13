/*
 * Create by Spreadst for secure boot
 */
#ifndef _SPRD_SB_VERIFIER_FSMGR_H
#define _SPRD_SB_VERIFIER_FSMGR_H

#ifdef __cplusplus
extern "C" {
#endif
const char *get_secureboot_for_device(const char *device);
void get_previous_secureboot_for_device(char *device, char **previous_dev,
          char **previous_type, char **previous_fstype);
unsigned char *get_previous_data_for_device(char *fstype, char *partition, int *size);
#ifdef __cplusplus
}
#endif


#endif  /* _SPRD_SB_VERIFIER_FSMGR_H */
