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

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "common.h"
#include "install.h"
#include "mincrypt/rsa.h"
#include "minui/minui.h"
#include "minzip/SysUtil.h"
#include "minzip/Zip.h"
#include "mtdutils/mounts.h"
#include "mtdutils/mtdutils.h"
#include "roots.h"
#include "verifier.h"
#include "ui.h"

extern RecoveryUI* ui;

#define ASSUMED_UPDATE_BINARY_NAME  "META-INF/com/google/android/update-binary"
#define PUBLIC_KEYS_FILE "/res/keys"

#define RECOVERY_FILEMOUNT_FAILURE   3013
#define RECOVERY_FILEMAP_FAILURE     3014
#define RECOVERY_KEYLOADED_FAILURE   3015
#define RECOVERY_BINARY_FAILURE      3016
#define RECOVERY_PARTITIONWRITE_FAILURE   3017
#define RECOVERY_FILECREATE_FAILURE  3018
#define RECOVERY_FILECOPY_FAILURE    3019
#define RECOVERY_BATTERY_LOW         3020
#define RECOVERY_ZIPVERIFIED_FAILURE 3021
#define RECOVERY_ZIPOPENED_FAILURE   3022

#define BATTERY_CAPCITY_FILE "/sys/class/power_supply/battery/capacity"
#define BATTERY_STATUS_FILE  "/sys/class/power_supply/battery/status"
// GmsCore enters recovery mode to install package when having enough battery
// percentage. Normally, the threshold is 20% without charger and 15% with charger.
// So we should check battery with a slightly lower limitation.
#define BATTERY_OK_PERCENTAGE 20
#define BATTERY_WITH_CHARGER_OK_PERCENTAGE 15

// Default allocation of progress bar segments to operations
static const int VERIFICATION_PROGRESS_TIME = 12;
static const float VERIFICATION_PROGRESS_FRACTION = 0.1;
static const float DEFAULT_FILES_PROGRESS_FRACTION = 0.4;
static const float DEFAULT_IMAGE_PROGRESS_FRACTION = 0.1;

// If the package contains an update binary, extract it and run it.
static int
try_update_binary(const char* path, ZipArchive* zip, bool* wipe_cache, unsigned int* err_no) {
    const ZipEntry* binary_entry =
            mzFindZipEntry(zip, ASSUMED_UPDATE_BINARY_NAME);
    if (binary_entry == NULL) {
        mzCloseZipArchive(zip);
        if (err_no != NULL) *err_no = RECOVERY_BINARY_FAILURE;
        return INSTALL_CORRUPT;
    }

    const char* binary = "/tmp/update_binary";
    unlink(binary);
    int fd = creat(binary, 0755);
    if (fd < 0) {
        mzCloseZipArchive(zip);
        LOGE("Can't make %s\n", binary);
        if (err_no != NULL) *err_no = RECOVERY_FILECREATE_FAILURE;
        return INSTALL_ERROR;
    }
    bool ok = mzExtractZipEntryToFile(zip, binary_entry, fd);
    close(fd);
    mzCloseZipArchive(zip);

    if (!ok) {
        LOGE("Can't copy %s\n", ASSUMED_UPDATE_BINARY_NAME);
        if (err_no != NULL) *err_no = RECOVERY_FILECOPY_FAILURE;
        return INSTALL_ERROR;
    }

    int pipefd[2];
    pipe(pipefd);

    // When executing the update binary contained in the package, the
    // arguments passed are:
    //
    //   - the version number for this interface
    //
    //   - an fd to which the program can write in order to update the
    //     progress bar.  The program can write single-line commands:
    //
    //        progress <frac> <secs>
    //            fill up the next <frac> part of of the progress bar
    //            over <secs> seconds.  If <secs> is zero, use
    //            set_progress commands to manually control the
    //            progress of this segment of the bar.
    //
    //        set_progress <frac>
    //            <frac> should be between 0.0 and 1.0; sets the
    //            progress bar within the segment defined by the most
    //            recent progress command.
    //
    //        firmware <"hboot"|"radio"> <filename>
    //            arrange to install the contents of <filename> in the
    //            given partition on reboot.
    //
    //            (API v2: <filename> may start with "PACKAGE:" to
    //            indicate taking a file from the OTA package.)
    //
    //            (API v3: this command no longer exists.)
    //
    //        ui_print <string>
    //            display <string> on the screen.
    //
    //        wipe_cache
    //            a wipe of cache will be performed following a successful
    //            installation.
    //
    //        clear_display
    //            turn off the text display.
    //
    //        enable_reboot
    //            packages can explicitly request that they want the user
    //            to be able to reboot during installation (useful for
    //            debugging packages that don't exit).
    //
    //   - the name of the package zip file.
    //

    const char** args = (const char**)malloc(sizeof(char*) * 5);
    args[0] = binary;
    args[1] = EXPAND(RECOVERY_API_VERSION);   // defined in Android.mk
    char* temp = (char*)malloc(10);
    sprintf(temp, "%d", pipefd[1]);
    args[2] = temp;
    args[3] = (char*)path;
    args[4] = NULL;

    pid_t pid = fork();
    if (pid == 0) {
        umask(022);
        close(pipefd[0]);
        execv(binary, (char* const*)args);
        fprintf(stdout, "E:Can't run %s (%s)\n", binary, strerror(errno));
        _exit(-1);
    }
    close(pipefd[1]);

    *wipe_cache = false;

    char buffer[1024];
    FILE* from_child = fdopen(pipefd[0], "r");
    while (fgets(buffer, sizeof(buffer), from_child) != NULL) {
        char* command = strtok(buffer, " \n");
        if (command == NULL) {
            continue;
        } else if (strcmp(command, "progress") == 0) {
            char* fraction_s = strtok(NULL, " \n");
            char* seconds_s = strtok(NULL, " \n");

            float fraction = strtof(fraction_s, NULL);
            int seconds = strtol(seconds_s, NULL, 10);

            ui->ShowProgress(fraction * (1-VERIFICATION_PROGRESS_FRACTION), seconds);
        } else if (strcmp(command, "set_progress") == 0) {
            char* fraction_s = strtok(NULL, " \n");
            float fraction = strtof(fraction_s, NULL);
            ui->SetProgress(fraction);
        } else if (strcmp(command, "ui_print") == 0) {
            char* str = strtok(NULL, "\n");
            if (str) {
                ui->Print("%s", str);
            } else {
                ui->Print("\n");
            }
            fflush(stdout);
        } else if (strcmp(command, "wipe_cache") == 0) {
            *wipe_cache = true;
        } else if (strcmp(command, "clear_display") == 0) {
            ui->SetBackground(RecoveryUI::NONE);
        } else if (strcmp(command, "enable_reboot") == 0) {
            // packages can explicitly request that they want the user
            // to be able to reboot during installation (useful for
            // debugging packages that don't exit).
            ui->SetEnableReboot(true);
        } else if (strcmp(command, "log") == 0) {
            // Save the logging request from updater and write to
            // result txt file later.
            char* line = strtok(NULL, "\n");
            sscanf(line, "error: %u", err_no);
            printf("%s\n",line);
        } else {
            LOGE("unknown command [%s]\n", command);
        }
    }
    fclose(from_child);

    int status;
    waitpid(pid, &status, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        LOGE("Error in %s\n(Status %d)\n", path, WEXITSTATUS(status));
        return INSTALL_ERROR;
    }

    return INSTALL_SUCCESS;
}

static int
really_install_package(const char *path, bool* wipe_cache, bool needs_mount, unsigned int* err_no)
{
    ui->SetBackground(RecoveryUI::INSTALLING_UPDATE);
    ui->Print("Finding update package...\n");
    // Give verification half the progress bar...
    ui->SetProgressType(RecoveryUI::DETERMINATE);
    ui->ShowProgress(VERIFICATION_PROGRESS_FRACTION, VERIFICATION_PROGRESS_TIME);
    LOGI("Update location: %s\n", path);

    // Map the update package into memory.
    ui->Print("Opening update package...\n");

    if (path && needs_mount) {
        if (path[0] == '@') {
            ensure_path_mounted(path+1);
        } else {
            ensure_path_mounted(path);
        }
    }

    MemMapping map;
    if (sysMapFile(path, &map) != 0) {
        LOGE("failed to map file\n");
        if (err_no != NULL) *err_no = RECOVERY_FILEMAP_FAILURE;
        return INSTALL_CORRUPT;
    }

    int numKeys;
    Certificate* loadedKeys = load_keys(PUBLIC_KEYS_FILE, &numKeys);
    if (loadedKeys == NULL) {
        LOGE("Failed to load keys\n");
        if (err_no != NULL) *err_no = RECOVERY_KEYLOADED_FAILURE;
        return INSTALL_CORRUPT;
    }
    LOGI("%d key(s) loaded from %s\n", numKeys, PUBLIC_KEYS_FILE);

    ui->Print("Verifying update package...\n");

    int err;
    err = verify_file(map.addr, map.length, loadedKeys, numKeys);
    free(loadedKeys);
    LOGI("verify_file returned %d\n", err);
    if (err != VERIFY_SUCCESS) {
        LOGE("signature verification failed\n");
        sysReleaseMap(&map);
        if (err_no != NULL) *err_no = RECOVERY_ZIPVERIFIED_FAILURE;
        return INSTALL_CORRUPT;
    }

    /* Try to open the package.
     */
    ZipArchive zip;
    err = mzOpenZipArchive(map.addr, map.length, &zip);
    if (err != 0) {
        LOGE("Can't open %s\n(%s)\n", path, err != -1 ? strerror(err) : "bad");
        sysReleaseMap(&map);
        if (err_no != NULL) *err_no = RECOVERY_ZIPOPENED_FAILURE;
        return INSTALL_CORRUPT;
    }

    /* Verify and install the contents of the package.
     */
    ui->Print("Installing update...\n");
    ui->SetEnableReboot(false);
    int result = try_update_binary(path, &zip, wipe_cache, err_no);
    ui->SetEnableReboot(true);
    ui->Print("\n");

    sysReleaseMap(&map);

    return result;
}
/* SPRD: write uboot and spl partition {@ */
int write_file(const char* path, const char *buff) {
    if (path == NULL) {
        return 0;
    }

    int fd = open(path, O_WRONLY);
    if (fd == -1) {
        return 0;
    }

    if (write(fd, buff, strlen(buff)) == -1) {
        close(fd);
        return 0;
    }
    close(fd);
    return 1;
}

int write_force_ro(void) {
    int ret1, ret2;
    ret1 = ret2 = 0;
    int utime = 0;
    const char *path_boot0 = "/sys/block/mmcblk0boot0/force_ro";
    const char *path_boot1 = "/sys/block/mmcblk0boot1/force_ro";
    do {
        ret1 = write_file(path_boot0, "0");
        ret2 = write_file(path_boot1, "0");

    if (ret1 && ret2) {
        return 1;
    } else {
        usleep(50000);// sleep 50ms
    }
    utime ++;
    } while (utime < 100);// timeout 5s
    LOGE("write force ro failed! \n");

    return 0;
}
/* @} */
static int readFromFile(const char* path, char* buf, size_t size) {
    char *cp = NULL;

    if (path == NULL || strlen(path) == 0)
        return -1;
    int fd = open(path, O_RDONLY, 0);
    if (fd < 0) {
        printf("Could not open '%s'\n", path);
        return -1;
    }

    ssize_t count = read(fd, buf, size);
    close(fd);
    return count;
}

static bool is_battery_ok() {
  char buf[64] = {0};
  int capacity = 0;
  bool charged = false;
  int i = 0;

  while (i < 5 && readFromFile(BATTERY_CAPCITY_FILE,buf,64) <= 0) {
     sleep(1);
     i++;
  }
  if (i < 5) {
    sscanf(buf,"%d",&capacity);
  } else {
    return false;
  }
  printf("The left battery capcity:%d\n",capacity);
  memset(buf,0,64);
  readFromFile(BATTERY_STATUS_FILE,buf,64);
  printf("The battery status:%s\n",buf);
  charged = (strcmp(buf,"Charging") == 0);
  return ((capacity >= BATTERY_OK_PERCENTAGE) || (charged && capacity >= BATTERY_WITH_CHARGER_OK_PERCENTAGE));
}
int
install_package(const char* path, bool* wipe_cache, const char* install_file,
                bool needs_mount, unsigned int* err_no)
{
    modified_flash = true;

    if (is_battery_ok() == false) {
        if (err_no != NULL) *err_no = RECOVERY_BATTERY_LOW;
        return INSTALL_ERROR;
    }
    /*SPRD: write uboot and spl partition {@ */
    if (write_force_ro() == 0) {
	    if (err_no != NULL) *err_no = RECOVERY_PARTITIONWRITE_FAILURE;
        return INSTALL_ERROR;
    }
    /* @} */
    FILE* install_log = fopen_path(install_file, "w");
    if (install_log) {
        fputs(path, install_log);
        fputc('\n', install_log);
    } else {
        LOGE("failed to open last_install: %s\n", strerror(errno));
    }
    int result;
    if (setup_install_mounts() != 0) {
        LOGE("failed to set up expected mounts for install; aborting\n");
        if (err_no != NULL) *err_no = RECOVERY_FILEMOUNT_FAILURE;
        result = INSTALL_ERROR;
    } else {
        result = really_install_package(path, wipe_cache, needs_mount,err_no);
    }
    if (install_log) {
        fputc(result == INSTALL_SUCCESS ? '1' : '0', install_log);
        fputc('\n', install_log);
        fclose(install_log);
    }
    return result;
}
