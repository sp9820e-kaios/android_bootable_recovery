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
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <limits.h>
#include <linux/input.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/klog.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

#include <base/file.h>
#include <base/stringprintf.h>

#include "cutils/hashmap.h"
#include "mincrypt/sha.h"
#include "bootloader.h"
#include "common.h"
#include "cutils/properties.h"
#include "cutils/android_reboot.h"
#include "install.h"
#include "minui/minui.h"
#include "minzip/DirUtil.h"
#include "roots.h"
#include "ui.h"
#include "screen_ui.h"
#include "device.h"
#include "adb_install.h"
#include "adb.h"
#include "fuse_sideload.h"
#include "fuse_sdcard_provider.h"
#include "private/android_filesystem_config.h"
//SPRD: add time info
extern "C" {
#include "show_info.h"
}
// SPRD: modify for support ubi
#include "ubiutils/ubiutils.h"

/* SPRD: add fota support { */
#ifdef FOTA_UPDATE_SUPPORT
extern "C" {
extern void fota_update_install_finish(const char* path, int status);
extern void finish_fota_update(const char* path, const char* source);
extern char* find_update_package(const char* path);
}
static int perform_fota = 0;
#endif
/* } */

struct selabel_handle *sehandle;

static const struct option OPTIONS[] = {
  { "send_intent", required_argument, NULL, 'i' },
  { "update_package", required_argument, NULL, 'u' },
  { "wipe_data", no_argument, NULL, 'w' },
  { "wipe_cache", no_argument, NULL, 'c' },
  { "show_text", no_argument, NULL, 't' },
  { "sideload", no_argument, NULL, 's' },
  { "sideload_auto_reboot", no_argument, NULL, 'a' },
  { "just_exit", no_argument, NULL, 'x' },
  { "locale", required_argument, NULL, 'l' },
  { "stages", required_argument, NULL, 'g' },
  { "shutdown_after", no_argument, NULL, 'p' },
  { "reason", required_argument, NULL, 'r' },
  { "system_partition_check", no_argument, NULL, 'e' },
  { NULL, 0, NULL, 0 },
};

static const char *CACHE_LOG_DIR = "/cache/recovery";
static const char *COMMAND_FILE = "/cache/recovery/command";
static const char *INTENT_FILE = "/cache/recovery/intent";
static const char *LOG_FILE = "/cache/recovery/log";
static const char *LAST_INSTALL_FILE = "/cache/recovery/last_install";
static const char *LOCALE_FILE = "/cache/recovery/last_locale";
static const char *CACHE_ROOT = "/cache";
//static const char *SDCARD_ROOT = "/sdcard";
/*SPRD:add for storage path as same as android @{
@orig
static const char *SDCARD_ROOT = "/sdcard";
*/
#ifdef ENABLE_INTERNAL_STORAGE
static const char *INTERNAL_STORAGE_ROOT = "/storage/sdcard0";
static const char *SDCARD_ROOT = "/storage/sdcard1";
#else
static const char *INTERNAL_STORAGE_ROOT = NULL;
static const char *SDCARD_ROOT = "/storage/sdcard0";
#endif
/*@}*/
static const char *TEMPORARY_LOG_FILE = "/tmp/recovery.log";
static const char *TEMPORARY_INSTALL_FILE = "/tmp/last_install";
static const char *LAST_KMSG_FILE = "/cache/recovery/last_kmsg";
static const char *LAST_LOG_FILE = "/cache/recovery/last_log";
static const char *JRD_FOTA_RESULT_FILE = "/data/fota/result.txt";
static const int KEEP_LOG_COUNT = 10;

RecoveryUI* ui = NULL;
char* locale = NULL;
char* stage = NULL;
char* reason = NULL;
bool modified_flash = false;
static unsigned int err_no = 0;

void check_system_root(RecoveryUI* ui_);
/*
 * The recovery tool communicates with the main system through /cache files.
 *   /cache/recovery/command - INPUT - command line for tool, one arg per line
 *   /cache/recovery/log - OUTPUT - combined log file from recovery run(s)
 *   /cache/recovery/intent - OUTPUT - intent that was passed in
 *
 * The arguments which may be supplied in the recovery.command file:
 *   --send_intent=anystring - write the text out to recovery.intent
 *   --update_package=path - verify install an OTA package file
 *   --wipe_data - erase user data (and cache), then reboot
 *   --wipe_cache - wipe cache (but not user data), then reboot
 *   --set_encrypted_filesystem=on|off - enables / diasables encrypted fs
 *   --just_exit - do nothing; exit and reboot
 *
 * After completing, we remove /cache/recovery/command and reboot.
 * Arguments may also be supplied in the bootloader control block (BCB).
 * These important scenarios must be safely restartable at any point:
 *
 * FACTORY RESET
 * 1. user selects "factory reset"
 * 2. main system writes "--wipe_data" to /cache/recovery/command
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--wipe_data"
 *    -- after this, rebooting will restart the erase --
 * 5. erase_volume() reformats /data
 * 6. erase_volume() reformats /cache
 * 7. finish_recovery() erases BCB
 *    -- after this, rebooting will restart the main system --
 * 8. main() calls reboot() to boot main system
 *
 * OTA INSTALL
 * 1. main system downloads OTA package to /cache/some-filename.zip
 * 2. main system writes "--update_package=/cache/some-filename.zip"
 * 3. main system reboots into recovery
 * 4. get_args() writes BCB with "boot-recovery" and "--update_package=..."
 *    -- after this, rebooting will attempt to reinstall the update --
 * 5. install_package() attempts to install the update
 *    NOTE: the package install must itself be restartable from any point
 * 6. finish_recovery() erases BCB
 *    -- after this, rebooting will (try to) restart the main system --
 * 7. ** if install failed **
 *    7a. prompt_and_wait() shows an error icon and waits for the user
 *    7b; the user reboots (pulling the battery, etc) into the main system
 * 8. main() calls maybe_install_firmware_update()
 *    ** if the update contained radio/hboot firmware **:
 *    8a. m_i_f_u() writes BCB with "boot-recovery" and "--wipe_cache"
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8b. m_i_f_u() writes firmware image into raw cache partition
 *    8c. m_i_f_u() writes BCB with "update-radio/hboot" and "--wipe_cache"
 *        -- after this, rebooting will attempt to reinstall firmware --
 *    8d. bootloader tries to flash firmware
 *    8e. bootloader writes BCB with "boot-recovery" (keeping "--wipe_cache")
 *        -- after this, rebooting will reformat cache & restart main system --
 *    8f. erase_volume() reformats /cache
 *    8g. finish_recovery() erases BCB
 *        -- after this, rebooting will (try to) restart the main system --
 * 9. main() calls reboot() to boot main system
 */

static const int MAX_ARG_LENGTH = 4096;
static const int MAX_ARGS = 100;

// open a given path, mounting partitions as necessary
FILE*
fopen_path(const char *path, const char *mode) {
    if (ensure_path_mounted(path) != 0) {
        LOGE("Can't mount %s\n", path);
        return NULL;
    }

    // When writing, try to create the containing directory, if necessary.
    // Use generous permissions, the system (init.rc) will reset them.
    if (strchr("wa", mode[0])) dirCreateHierarchy(path, 0777, NULL, 1, sehandle);

    FILE *fp = fopen(path, mode);
    return fp;
}

bool is_ro_debuggable() {
    char value[PROPERTY_VALUE_MAX+1];
    return (property_get("ro.debuggable", value, NULL) == 1 && value[0] == '1');
}

static void redirect_stdio(const char* filename) {
    // If these fail, there's not really anywhere to complain...
    freopen(filename, "a", stdout); setbuf(stdout, NULL);
    freopen(filename, "a", stderr); setbuf(stderr, NULL);
}

// close a file, log an error if the error indicator is set
static void
check_and_fclose(FILE *fp, const char *name) {
    fflush(fp);
    if (ferror(fp)) LOGE("Error in %s\n(%s)\n", name, strerror(errno));
    fclose(fp);
}

// command line args come from, in decreasing precedence:
//   - the actual command line
//   - the bootloader control block (one per line, after "recovery")
//   - the contents of COMMAND_FILE (one per line)
static void
get_args(int *argc, char ***argv) {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    get_bootloader_message(&boot);  // this may fail, leaving a zeroed structure
    stage = strndup(boot.stage, sizeof(boot.stage));

    if (boot.command[0] != 0 && boot.command[0] != 255) {
        LOGI("Boot command: %.*s\n", (int)sizeof(boot.command), boot.command);
    }

    if (boot.status[0] != 0 && boot.status[0] != 255) {
        LOGI("Boot status: %.*s\n", (int)sizeof(boot.status), boot.status);
    }

    // --- if arguments weren't supplied, look in the bootloader control block
    if (*argc <= 1) {
        boot.recovery[sizeof(boot.recovery) - 1] = '\0';  // Ensure termination
        const char *arg = strtok(boot.recovery, "\n");
        if (arg != NULL && !strcmp(arg, "recovery")) {
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = strdup(arg);
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if ((arg = strtok(NULL, "\n")) == NULL) break;
                (*argv)[*argc] = strdup(arg);
            }
            LOGI("Got arguments from boot message\n");
        } else if (boot.recovery[0] != 0 && boot.recovery[0] != 255) {
            LOGE("Bad boot message\n\"%.20s\"\n", boot.recovery);
        }
    }

    // --- if that doesn't work, try the command file
    if (*argc <= 1) {
        FILE *fp = fopen_path(COMMAND_FILE, "r");
        if (fp != NULL) {
            char *token;
            char *argv0 = (*argv)[0];
            *argv = (char **) malloc(sizeof(char *) * MAX_ARGS);
            (*argv)[0] = argv0;  // use the same program name

            char buf[MAX_ARG_LENGTH];
            for (*argc = 1; *argc < MAX_ARGS; ++*argc) {
                if (!fgets(buf, sizeof(buf), fp)) break;
                token = strtok(buf, "\r\n");
                if (token != NULL) {
                    (*argv)[*argc] = strdup(token);  // Strip newline.
                } else {
                    --*argc;
                }
            }

            check_and_fclose(fp, COMMAND_FILE);
            LOGI("Got arguments from %s\n", COMMAND_FILE);
        }
    }

    // --> write the arguments we have back into the bootloader control block
    // always boot into recovery after this (until finish_recovery() is called)
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    int i;
    for (i = 1; i < *argc; ++i) {
        strlcat(boot.recovery, (*argv)[i], sizeof(boot.recovery));
        strlcat(boot.recovery, "\n", sizeof(boot.recovery));
    }
    set_bootloader_message(&boot);
}

static void
set_sdcard_update_bootloader_message() {
    struct bootloader_message boot;
    memset(&boot, 0, sizeof(boot));
    strlcpy(boot.command, "boot-recovery", sizeof(boot.command));
    strlcpy(boot.recovery, "recovery\n", sizeof(boot.recovery));
    set_bootloader_message(&boot);
}

// Read from kernel log into buffer and write out to file.
static void save_kernel_log(const char* destination) {
    int klog_buf_len = klogctl(KLOG_SIZE_BUFFER, 0, 0);
    if (klog_buf_len <= 0) {
        LOGE("Error getting klog size: %s\n", strerror(errno));
        return;
    }

    std::string buffer(klog_buf_len, 0);
    int n = klogctl(KLOG_READ_ALL, &buffer[0], klog_buf_len);
    if (n == -1) {
        LOGE("Error in reading klog: %s\n", strerror(errno));
        return;
    }
    buffer.resize(n);
    android::base::WriteStringToFile(buffer, destination);
}

// How much of the temp log we have copied to the copy in cache.
static long tmplog_offset = 0;

static void copy_log_file(const char* source, const char* destination, bool append) {
    FILE* dest_fp = fopen_path(destination, append ? "a" : "w");
    if (dest_fp == nullptr) {
        LOGE("Can't open %s\n", destination);
    } else {
        FILE* source_fp = fopen(source, "r");
        if (source_fp != nullptr) {
            if (append) {
                fseek(source_fp, tmplog_offset, SEEK_SET);  // Since last write
            }
            char buf[4096];
            size_t bytes;
            while ((bytes = fread(buf, 1, sizeof(buf), source_fp)) != 0) {
                fwrite(buf, 1, bytes, dest_fp);
            }
            if (append) {
                tmplog_offset = ftell(source_fp);
            }
            check_and_fclose(source_fp, source);
        }
        check_and_fclose(dest_fp, destination);
    }
}

// Rename last_log -> last_log.1 -> last_log.2 -> ... -> last_log.$max.
// Similarly rename last_kmsg -> last_kmsg.1 -> ... -> last_kmsg.$max.
// Overwrite any existing last_log.$max and last_kmsg.$max.
static void rotate_logs(int max) {
    // Logs should only be rotated once.
    static bool rotated = false;
    if (rotated) {
        return;
    }
    rotated = true;
    ensure_path_mounted(LAST_LOG_FILE);
    ensure_path_mounted(LAST_KMSG_FILE);

    for (int i = max-1; i >= 0; --i) {
        std::string old_log = android::base::StringPrintf((i == 0) ? "%s" : "%s.%d",
                LAST_LOG_FILE, i);
        std::string new_log = android::base::StringPrintf("%s.%d", LAST_LOG_FILE, i+1);
        // Ignore errors if old_log doesn't exist.
        rename(old_log.c_str(), new_log.c_str());

        std::string old_kmsg = android::base::StringPrintf((i == 0) ? "%s" : "%s.%d",
                LAST_KMSG_FILE, i);
        std::string new_kmsg = android::base::StringPrintf("%s.%d", LAST_KMSG_FILE, i+1);
        rename(old_kmsg.c_str(), new_kmsg.c_str());
    }
}

static void copy_logs() {
    // We only rotate and record the log of the current session if there are
    // actual attempts to modify the flash, such as wipes, installs from BCB
    // or menu selections. This is to avoid unnecessary rotation (and
    // possible deletion) of log files, if it does not do anything loggable.
    if (!modified_flash) {
        return;
    }

    rotate_logs(KEEP_LOG_COUNT);

    // Copy logs to cache so the system can find out what happened.
    copy_log_file(TEMPORARY_LOG_FILE, LOG_FILE, true);
    copy_log_file(TEMPORARY_LOG_FILE, LAST_LOG_FILE, false);
    copy_log_file(TEMPORARY_INSTALL_FILE, LAST_INSTALL_FILE, false);
    save_kernel_log(LAST_KMSG_FILE);
    chmod(LOG_FILE, 0600);
    chown(LOG_FILE, 1000, 1000);   // system user
    chmod(LAST_KMSG_FILE, 0600);
    chown(LAST_KMSG_FILE, 1000, 1000);   // system user
    chmod(LAST_LOG_FILE, 0640);
    chmod(LAST_INSTALL_FILE, 0644);
    sync();
}

// clear the recovery command and prepare to boot a (hopefully working) system,
// copy our log file to cache as well (for the system to read), and
// record any intent we were asked to communicate back to the system.
// this function is idempotent: call it as many times as you like.
static void
finish_recovery(const char *send_intent) {
    // By this point, we're ready to return to the main system...
    if (send_intent != NULL) {
        FILE *fp = fopen_path(INTENT_FILE, "w");
        if (fp == NULL) {
            LOGE("Can't open %s\n", INTENT_FILE);
        } else {
            fputs(send_intent, fp);
            check_and_fclose(fp, INTENT_FILE);
        }
    }

    // Save the locale to cache, so if recovery is next started up
    // without a --locale argument (eg, directly from the bootloader)
    // it will use the last-known locale.
    if (locale != NULL) {
        LOGI("Saving locale \"%s\"\n", locale);
        FILE* fp = fopen_path(LOCALE_FILE, "w");
        fwrite(locale, 1, strlen(locale), fp);
        fflush(fp);
        fsync(fileno(fp));
        check_and_fclose(fp, LOCALE_FILE);
    }

    copy_logs();

    // Reset to normal system boot so recovery won't cycle indefinitely.
    if (err_no != 3020) {
      /*3020: low battery, should not clean*/
      struct bootloader_message boot;
      memset(&boot, 0, sizeof(boot));
      set_bootloader_message(&boot);

      // Remove the command file, so recovery won't repeat indefinitely.
      if (ensure_path_mounted(COMMAND_FILE) != 0 ||
        (unlink(COMMAND_FILE) && errno != ENOENT)) {
        LOGW("Can't unlink %s\n", COMMAND_FILE);
      }
    }

    ensure_path_unmounted(CACHE_ROOT);
    sync();  // For good measure.
}

typedef struct _saved_log_file {
    char* name;
    struct stat st;
    unsigned char* data;
    struct _saved_log_file* next;
} saved_log_file;

static bool erase_volume(const char* volume) {
    bool is_cache = (strcmp(volume, CACHE_ROOT) == 0);

    ui->SetBackground(RecoveryUI::ERASING);
    ui->SetProgressType(RecoveryUI::INDETERMINATE);

    saved_log_file* head = NULL;

    if (is_cache) {
        // If we're reformatting /cache, we load any past logs
        // (i.e. "/cache/recovery/last_*") and the current log
        // ("/cache/recovery/log") into memory, so we can restore them after
        // the reformat.

        ensure_path_mounted(volume);

        DIR* d;
        struct dirent* de;
        d = opendir(CACHE_LOG_DIR);
        if (d) {
            char path[PATH_MAX];
            strcpy(path, CACHE_LOG_DIR);
            strcat(path, "/");
            int path_len = strlen(path);
            while ((de = readdir(d)) != NULL) {
                if (strncmp(de->d_name, "last_", 5) == 0 || strcmp(de->d_name, "log") == 0) {
                    saved_log_file* p = (saved_log_file*) malloc(sizeof(saved_log_file));
                    strcpy(path+path_len, de->d_name);
                    p->name = strdup(path);
                    if (stat(path, &(p->st)) == 0) {
                        // truncate files to 512kb
                        if (p->st.st_size > (1 << 19)) {
                            p->st.st_size = 1 << 19;
                        }
                        p->data = (unsigned char*) malloc(p->st.st_size);
                        FILE* f = fopen(path, "rb");
                        fread(p->data, 1, p->st.st_size, f);
                        fclose(f);
                        p->next = head;
                        head = p;
                    } else {
                        free(p);
                    }
                }
            }
            closedir(d);
        } else {
            if (errno != ENOENT) {
                printf("opendir failed: %s\n", strerror(errno));
            }
        }
    }

    ui->Print("Formatting %s...\n", volume);

    ensure_path_unmounted(volume);
    //SPRD add time info for format device
    printf("start format :%s\n",volume);

    int result = format_volume(volume);
    //SPRD add time info for format device
    printf("end format :%s\n",volume);

    if (is_cache) {
        while (head) {
            FILE* f = fopen_path(head->name, "wb");
            if (f) {
                fwrite(head->data, 1, head->st.st_size, f);
                fclose(f);
                chmod(head->name, head->st.st_mode);
                chown(head->name, head->st.st_uid, head->st.st_gid);
            }
            free(head->name);
            free(head->data);
            saved_log_file* temp = head->next;
            free(head);
            head = temp;
        }

        // Any part of the log we'd copied to cache is now gone.
        // Reset the pointer so we copy from the beginning of the temp
        // log.
        tmplog_offset = 0;
        copy_logs();
    }

    return (result == 0);
}

static int
get_menu_selection(const char* const * headers, const char* const * items,
                   int menu_only, int initial_selection, Device* device) {
    // throw away keys pressed previously, so user doesn't
    // accidentally trigger menu items.
    ui->FlushKeys();

    ui->StartMenu(headers, items, initial_selection);
    int selected = initial_selection;
    int chosen_item = -1;

    while (chosen_item < 0) {
        int key = ui->WaitKey();
        int visible = ui->IsTextVisible();

        if (key == -1) {   // ui_wait_key() timed out
            if (ui->WasTextEverVisible()) {
                continue;
            } else {
                LOGI("timed out waiting for key input; rebooting.\n");
                ui->EndMenu();
                return 0; // XXX fixme
            }
        }

        int action = device->HandleMenuKey(key, visible);

        if (action < 0) {
            switch (action) {
                case Device::kHighlightUp:
                    selected = ui->SelectMenu(--selected);
                    break;
                case Device::kHighlightDown:
                    selected = ui->SelectMenu(++selected);
                    break;
                case Device::kInvokeItem:
                    chosen_item = selected;
                    break;
                case Device::kNoAction:
                    break;
            }
        } else if (!menu_only) {
            chosen_item = action;
        }
    }

    ui->EndMenu();
    return chosen_item;
}

static int compare_string(const void* a, const void* b) {
    return strcmp(*(const char**)a, *(const char**)b);
}

// Returns a malloc'd path, or NULL.
static char* browse_directory(const char* path, Device* device) {
    ensure_path_mounted(path);

    DIR* d = opendir(path);
    if (d == NULL) {
        LOGE("error opening %s: %s\n", path, strerror(errno));
        return NULL;
    }

    int d_size = 0;
    int d_alloc = 10;
    char** dirs = (char**)malloc(d_alloc * sizeof(char*));
    int z_size = 1;
    int z_alloc = 10;
    char** zips = (char**)malloc(z_alloc * sizeof(char*));
    zips[0] = strdup("../");

    struct dirent* de;
    while ((de = readdir(d)) != NULL) {
        int name_len = strlen(de->d_name);

        if (de->d_type == DT_DIR) {
            // skip "." and ".." entries
            if (name_len == 1 && de->d_name[0] == '.') continue;
            if (name_len == 2 && de->d_name[0] == '.' &&
                de->d_name[1] == '.') continue;

            if (d_size >= d_alloc) {
                d_alloc *= 2;
                dirs = (char**)realloc(dirs, d_alloc * sizeof(char*));
            }
            dirs[d_size] = (char*)malloc(name_len + 2);
            strcpy(dirs[d_size], de->d_name);
            dirs[d_size][name_len] = '/';
            dirs[d_size][name_len+1] = '\0';
            ++d_size;
        } else if (de->d_type == DT_REG &&
                   name_len >= 4 &&
                   strncasecmp(de->d_name + (name_len-4), ".zip", 4) == 0) {
            if (z_size >= z_alloc) {
                z_alloc *= 2;
                zips = (char**)realloc(zips, z_alloc * sizeof(char*));
            }
            zips[z_size++] = strdup(de->d_name);
        }
    }
    closedir(d);

    qsort(dirs, d_size, sizeof(char*), compare_string);
    qsort(zips, z_size, sizeof(char*), compare_string);

    // append dirs to the zips list
    if (d_size + z_size + 1 > z_alloc) {
        z_alloc = d_size + z_size + 1;
        zips = (char**)realloc(zips, z_alloc * sizeof(char*));
    }
    memcpy(zips + z_size, dirs, d_size * sizeof(char*));
    free(dirs);
    z_size += d_size;
    zips[z_size] = NULL;

    const char* headers[] = { "Choose a package to install:", path, NULL };

    char* result;
    int chosen_item = 0;
    while (true) {
        chosen_item = get_menu_selection(headers, zips, 1, chosen_item, device);

        char* item = zips[chosen_item];
        int item_len = strlen(item);
        if (chosen_item == 0) {          // item 0 is always "../"
            // go up but continue browsing (if the caller is update_directory)
            result = NULL;
            break;
        }

        char new_path[PATH_MAX];
        strlcpy(new_path, path, PATH_MAX);
        strlcat(new_path, "/", PATH_MAX);
        strlcat(new_path, item, PATH_MAX);

        if (item[item_len-1] == '/') {
            // recurse down into a subdirectory
            new_path[strlen(new_path)-1] = '\0';  // truncate the trailing '/'
            result = browse_directory(new_path, device);
            if (result) break;
        } else {
            // selected a zip file: return the malloc'd path to the caller.
            result = strdup(new_path);
            break;
        }
    }

    for (int i = 0; i < z_size; ++i) free(zips[i]);
    free(zips);

    return result;
}

static bool yes_no(Device* device, const char* question1, const char* question2) {
    const char* headers[] = { question1, question2, NULL };
    const char* items[] = { " No", " Yes", NULL };

    int chosen_item = get_menu_selection(headers, items, 1, 0, device);
    return (chosen_item == 1);
}

static void erase_kaios_root_recorder(void)
{
    const char *path = "/sys/root_recorder/rootrecorder";
    const char buffer[5] = { 0 };

    FILE *f = fopen(path, "r+b");
	if (f) {
		fwrite(buffer, sizeof(buffer), 1, f);
		fclose(f);
	}

    return;
}
// Add for MDM recovery test at 2018-09-10 19:15:36 by peng.ding@kaiostech.com start
static void *load_mdm_file(const char * const partition, const char * const file_name, size_t *o_size)
{
  size_t buf_len = 0;
  void *ret_buffer = NULL;
  FILE *fp = NULL;

  if (NULL ==file_name) {
    return NULL;
  }

  ensure_path_mounted(partition);
  modified_flash = true;
  fp = fopen(file_name, "rb");
  if (NULL == fp) {
    return NULL;
  }

  while (1) {
    char buf[1024] = "";
    size_t size =  fread(buf, sizeof(char), sizeof(buf) - 1, fp);
    if (size <= 0) {
      if (ret_buffer) {
        ((char *)ret_buffer)[buf_len] = 0;
      }
      break;
    }
    void * tmp_buf = realloc(ret_buffer, size + buf_len + 1);
    if (tmp_buf) {
      ret_buffer = tmp_buf;
      memcpy(((char *)ret_buffer) + buf_len, buf, size);
      buf_len += size;
    }
    else {
      if (ret_buffer) {
        free(ret_buffer);
        ret_buffer = NULL;
      }
      break;
    }
  }
  fclose(fp);
  *o_size = buf_len;

  return ret_buffer;
}

static int store_mdm_file(const char * const partition, const char * const file_name, void *buffer, size_t size) {
  int ret = 0;
  FILE *fp = NULL;

  ensure_path_mounted(partition);
  modified_flash = true;

  fp = fopen (file_name, "wb");
  if (NULL == fp || NULL == buffer || size <= 0) {
    return ret;
  }
  ret = fwrite(buffer , sizeof(char), size, fp);
  fclose(fp);

  return (ret > 0);
}

static char * const get_partition(char *const partition, const char * const full_path) {
  if (partition && full_path && full_path[0] == '/') {
    partition[0] = '/';
    int i = 1;
    while ('/' != full_path[i] && 0 != full_path[i]) {
      partition[i] = full_path[i];
      i++;
    }
    partition[i] = 0;
  }
  return partition;
}

static bool move_mdm_file(const char* const src_path, const char *const dst_path) {
  size_t size = 0;
  char buf[512] = "";
  void *rbuf = load_mdm_file(get_partition(buf, src_path), src_path, &size);
  if (rbuf) {
    store_mdm_file(get_partition(buf, dst_path), dst_path, rbuf, size);
    free(rbuf);
    rbuf = NULL;
  }
  return true;
}

static bool backup_mdm_file() {
  return move_mdm_file("/data/.mdm_save.json", "/cache/.mdm_save.json");
}

static bool recover_mdm_file() {
  return move_mdm_file("/cache/.mdm_save.json", "/data/.mdm_save.json");
}
// Add for MDM recovery test at 2018-09-10 19:15:47 by peng.ding@kaiostech.com end
// Return true on success.
static bool wipe_data(int should_confirm, Device* device) {
    if (should_confirm && !yes_no(device, "Wipe all user data?", "  THIS CAN NOT BE UNDONE!")) {
        return false;
    }

    modified_flash = true;

    ui->Print("\n-- Wiping data...\n");
    bool success =
        device->PreWipeData() &&
        backup_mdm_file()     &&
        erase_volume("/data") &&
        recover_mdm_file()    &&
        erase_volume("/cache") &&
#ifdef HAVE_USBMSC_PARTITION	// Kaios usbmsc partition
        erase_volume("/usbmsc") &&
#endif
        device->PostWipeData();
    erase_kaios_root_recorder();
    ui->Print("Data wipe %s.\n", success ? "complete" : "failed");
    return success;
}

// Return true on success.
static bool wipe_cache(bool should_confirm, Device* device) {
    if (should_confirm && !yes_no(device, "Wipe cache?", "  THIS CAN NOT BE UNDONE!")) {
        return false;
    }

    modified_flash = true;

    ui->Print("\n-- Wiping cache...\n");
    bool success = erase_volume("/cache");
    ui->Print("Cache wipe %s.\n", success ? "complete" : "failed");
    return success;
}

static void choose_recovery_file(Device* device) {
    // "Back" + KEEP_LOG_COUNT * 2 + terminating nullptr entry
    char* entries[1 + KEEP_LOG_COUNT * 2 + 1];
    memset(entries, 0, sizeof(entries));

    unsigned int n = 0;

    // Add LAST_LOG_FILE + LAST_LOG_FILE.x
    // Add LAST_KMSG_FILE + LAST_KMSG_FILE.x
    for (int i = 0; i < KEEP_LOG_COUNT; i++) {
        char* log_file;
        if (asprintf(&log_file, (i == 0) ? "%s" : "%s.%d", LAST_LOG_FILE, i) == -1) {
            // memory allocation failure - return early. Should never happen.
            return;
        }
        if ((ensure_path_mounted(log_file) != 0) || (access(log_file, R_OK) == -1)) {
            free(log_file);
        } else {
            entries[n++] = log_file;
        }

        char* kmsg_file;
        if (asprintf(&kmsg_file, (i == 0) ? "%s" : "%s.%d", LAST_KMSG_FILE, i) == -1) {
            // memory allocation failure - return early. Should never happen.
            return;
        }
        if ((ensure_path_mounted(kmsg_file) != 0) || (access(kmsg_file, R_OK) == -1)) {
            free(kmsg_file);
        } else {
            entries[n++] = kmsg_file;
        }
    }

    entries[n++] = strdup("Back");

    const char* headers[] = { "Select file to view", nullptr };

    while (true) {
        int chosen_item = get_menu_selection(headers, entries, 1, 0, device);
        if (strcmp(entries[chosen_item], "Back") == 0) break;

        // TODO: do we need to redirect? ShowFile could just avoid writing to stdio.
        redirect_stdio("/dev/null");
        ui->ShowFile(entries[chosen_item]);
        redirect_stdio(TEMPORARY_LOG_FILE);
    }

    for (size_t i = 0; i < (sizeof(entries) / sizeof(*entries)); i++) {
        free(entries[i]);
    }
}

static int apply_from_sdcard(Device* device, bool* wipe_cache) {
    modified_flash = true;

    if (ensure_path_mounted(SDCARD_ROOT) != 0) {
        ui->Print("\n-- Couldn't mount %s.\n", SDCARD_ROOT);
        return INSTALL_ERROR;
    }

    char* path = browse_directory(SDCARD_ROOT, device);
    if (path == NULL) {
        ui->Print("\n-- No package file selected.\n");
        return INSTALL_ERROR;
    }

    ui->Print("\n-- Install %s ...\n", path);
    set_sdcard_update_bootloader_message();
     /* SPRD: modify for disable fuse @{ */
/*
 *    void* token = start_sdcard_fuse(path);
 *
 *    int status = install_package(FUSE_SIDELOAD_HOST_PATHNAME, wipe_cache,
 *                                 TEMPORARY_INSTALL_FILE, false);
 *
 *    finish_sdcard_fuse(token);
 */
    /* @}*/
    int status = install_package(path, wipe_cache,
                                 TEMPORARY_INSTALL_FILE, false, NULL);
    ensure_path_unmounted(SDCARD_ROOT);
    return status;
}

// Return REBOOT, SHUTDOWN, or REBOOT_BOOTLOADER.  Returning NO_ACTION
// means to take the default, which is to reboot or shutdown depending
// on if the --shutdown_after flag was passed to recovery.
static Device::BuiltinAction
prompt_and_wait(Device* device, int status) {
    for (;;) {
        finish_recovery(NULL);
        switch (status) {
            case INSTALL_SUCCESS:
            case INSTALL_NONE:
                ui->SetBackground(RecoveryUI::NO_COMMAND);
                break;

            case INSTALL_ERROR:
            case INSTALL_CORRUPT:
                ui->SetBackground(RecoveryUI::ERROR);
                break;
        }
        ui->SetProgressType(RecoveryUI::EMPTY);

        int chosen_item = get_menu_selection(nullptr, device->GetMenuItems(), 0, 0, device);

        // device-specific code may take some action here.  It may
        // return one of the core actions handled in the switch
        // statement below.
        Device::BuiltinAction chosen_action = device->InvokeMenuItem(chosen_item);

        bool should_wipe_cache = false;
        switch (chosen_action) {
            case Device::NO_ACTION:
                break;

            case Device::REBOOT:
            case Device::SHUTDOWN:
            case Device::REBOOT_BOOTLOADER:
                return chosen_action;

            case Device::WIPE_DATA:
                wipe_data(ui->IsTextVisible(), device);
                if (!ui->IsTextVisible()) return Device::NO_ACTION;
                break;

            case Device::WIPE_CACHE:
                wipe_cache(ui->IsTextVisible(), device);
                if (!ui->IsTextVisible()) return Device::NO_ACTION;
                break;

            case Device::APPLY_ADB_SIDELOAD:
            case Device::APPLY_SDCARD:
                {
                    bool adb = (chosen_action == Device::APPLY_ADB_SIDELOAD);
                    if (adb) {
                        status = apply_from_adb(ui, &should_wipe_cache, TEMPORARY_INSTALL_FILE);
                    } else {
                        status = apply_from_sdcard(device, &should_wipe_cache);
                    }

                    if (status == INSTALL_SUCCESS && should_wipe_cache) {
                        if (!wipe_cache(false, device)) {
                            status = INSTALL_ERROR;
                        }
                    }

                    if (status != INSTALL_SUCCESS) {
                        ui->SetBackground(RecoveryUI::ERROR);
                        ui->Print("Installation aborted.\n");
                        copy_logs();
                    } else if (!ui->IsTextVisible()) {
                        return Device::NO_ACTION;  // reboot if logs aren't visible
                    } else {
                        ui->Print("\nInstall from %s complete.\n", adb ? "ADB" : "SD card");
                    }
                }
                break;

            case Device::APPLY_CACHE: {
                /*SPRD:update from cache partiton and internal storage @{
                @orig
                ui->Print("\nAPPLY_CACHE is deprecated.\n");

                break;

                */
                ensure_path_mounted(CACHE_ROOT);
                char* path = browse_directory(CACHE_ROOT, device);
                if (path == NULL) {
                    ui->Print("\n-- No package file selected.\n", path);
                    break;
                }

                ui->Print("\n-- Install %s ...\n", path);
                set_sdcard_update_bootloader_message();

                int status = install_package(path, &should_wipe_cache,
                                             TEMPORARY_INSTALL_FILE, false,NULL);

                ensure_path_unmounted(CACHE_ROOT);

                if (status == INSTALL_SUCCESS && should_wipe_cache) {
                    ui->Print("\n-- Wiping cache (at package request)...\n");
                    if (wipe_cache(false,device)){
                        ui->Print("Cache wipe failed.\n");
                    } else {
                        ui->Print("Cache wipe complete.\n");
                    }
                }

                if (status >= 0) {
                    if (status != INSTALL_SUCCESS) {
                        ui->SetBackground(RecoveryUI::ERROR);
                        ui->Print("Installation aborted.\n");
                    } else if (!ui->IsTextVisible()) {
                        return Device::NO_ACTION;  // reboot if logs aren't visible
                    } else {
                        ui->Print("\nInstall from cache complete.\n");
                    }
                }
                break;
            }

            case Device::APPLY_INT: {
                ensure_path_mounted(INTERNAL_STORAGE_ROOT);
                char * path = browse_directory(INTERNAL_STORAGE_ROOT, device);
                if (path == NULL) {
                    ui->Print("\n-- No package file selected.\n", path);
                    break;
                }

                ui->Print("\n-- Install %s ...\n", path);
                set_sdcard_update_bootloader_message();

                int status = install_package(path, &should_wipe_cache,
                                             TEMPORARY_INSTALL_FILE, false,NULL);

                ensure_path_unmounted(INTERNAL_STORAGE_ROOT);

                if (status == INSTALL_SUCCESS && should_wipe_cache) {
                    ui->Print("\n-- Wiping cache (at package request)...\n");
                    if (wipe_cache(false,device)){
                        ui->Print("Cache wipe failed.\n");
                    } else {
                        ui->Print("Cache wipe complete.\n");
                    }
                }

                if (status >= 0) {
                    if (status != INSTALL_SUCCESS) {
                        ui->SetBackground(RecoveryUI::ERROR);
                        ui->Print("Installation aborted.\n");
                    } else if (!ui->IsTextVisible()) {
                        return Device::NO_ACTION;  // reboot if logs aren't visible
                    } else {
                        ui->Print("\nInstall from internal storage complete.\n");
                    }
                }
                break;
            }
                /*@}*/


            case Device::VIEW_RECOVERY_LOGS:
                choose_recovery_file(device);
                break;

            case Device::MOUNT_SYSTEM:
                if (ensure_path_mounted("/system") != -1) {
                    ui->Print("Mounted /system.\n");
                }
                break;
             case Device::CHECK_ROOT:
                LOGW("enter check root");
                ui->Print("\n-- system partition mount \n");
                ensure_path_mounted("/system");
                check_system_root(ui);
                break;
        }
    }
}

static void
print_property(const char *key, const char *name, void *cookie) {
    printf("%s=%s\n", key, name);
}

static void
load_locale_from_cache() {
    FILE* fp = fopen_path(LOCALE_FILE, "r");
    char buffer[PROPERTY_VALUE_MAX] = {0};
    if (fp != NULL) {
        fgets(buffer, sizeof(buffer), fp);
        int j = 0;
        unsigned int i;
        for (i = 0; i < sizeof(buffer) && buffer[i]; ++i) {
            if (!isspace(buffer[i])) {
                buffer[j++] = buffer[i];
            }
        }
        buffer[j] = 0;
        locale = strdup(buffer);
        check_and_fclose(fp, LOCALE_FILE);
    } else {
        property_get("ro.product.locale", buffer, "");
        if (strlen(buffer) > 0) {
            locale = strdup(buffer);
        }
    }
    /*Set the default value*/
    if (locale == NULL) {
        locale = "en-US";
    }
}
static void fota_reset_status(void) {
    if(unlink(JRD_FOTA_RESULT_FILE)){
        LOGE("erasing fota.status failed errno=%d\n",errno);
    }
}
static void write_file(const char *file_name, int reason, char *result)
{
    char dir_name[256];
    char buf[256];

    ensure_path_mounted("/data");

    strcpy(dir_name, file_name);
    char *p = strrchr(dir_name, '/');
    *p = 0;

    fprintf(stdout, "dir_name = %s\n", dir_name);
    mode_t proc_mask = umask(0);

    if (opendir(dir_name) == NULL)  {
        fprintf(stdout, "dir_name = '%s' does not exist, create it.\n", dir_name);
        if (mkdir(dir_name, 0775))  {
            fprintf(stdout, "can not create '%s' : %s\n", dir_name, strerror(errno));
            umask(proc_mask);
            return;
        }
        chown(dir_name, AID_SYSTEM, AID_SYSTEM);
    }

    int result_fd = open(file_name, O_RDWR | O_CREAT | O_TRUNC, 0666);
    fchown(result_fd, AID_SYSTEM, AID_SYSTEM);

    if (result_fd < 0) {
        fprintf(stdout, "cannot open '%s' for output : %s\n", file_name, strerror(errno));
        umask(proc_mask);
        return;
    }

    sprintf(buf,"%s:%d",result,reason);

    write(result_fd, buf, strlen(buf));
    close(result_fd);
    umask(proc_mask);
}

static char *install_result = NULL;
static inline void set_install_result(char *s)
{
    install_result = s;
}
#define INSTALL_SUCCESS_CODE 999
#define INSTALL_FAILURE_CODE 1000
static void write_result(int reason, unsigned int code)
{
    unsigned int ret = 0;
    if (reason == INSTALL_SUCCESS) {
      ret = INSTALL_SUCCESS_CODE;
      set_install_result("INSTALL SUCCESS");
    } else {
      if (code != 0) {
        ret = code;
      } else {
        ret = INSTALL_FAILURE_CODE;
      }
      set_install_result("INSTALL Failed");
    }

    fprintf(stdout, "package install result:%s\n", install_result);
    write_file(JRD_FOTA_RESULT_FILE, ret, install_result);
}

static RecoveryUI* gCurrentUI = NULL;

void
ui_print(const char* format, ...) {
    char buffer[256];

    va_list ap;
    va_start(ap, format);
    vsnprintf(buffer, sizeof(buffer), format, ap);
    va_end(ap);

    if (gCurrentUI != NULL) {
        gCurrentUI->Print("%s", buffer);
    } else {
        fputs(buffer, stdout);
    }
}

static Hashmap* app_to_sha1_ori = NULL;
static Hashmap* app_to_sha1_ori_new = NULL;/*for the case ota update failure*/

#define BUFFER_SIZE 4096
static int do_sha1(const char *path,RecoveryUI* ui_,char *sha1_string)
{
    int fd;
    SHA_CTX sha1_ctx;
    int i = 0;
    ui =ui_;

    fd = open(path, O_RDONLY);
    if (fd < 0) {
        return -1;
    }

    SHA_init(&sha1_ctx);
    while (1) {
        char buf[BUFFER_SIZE];
        ssize_t rlen;
        rlen = read(fd, buf, sizeof(buf));
        if (rlen == 0)
            break;
        else if (rlen < 0) {
            (void)close(fd);
            return -1;
        }
        SHA_update(&sha1_ctx, buf, rlen);
    }

    if (close(fd)) {
        return -1;
    }

    const char* sha1 = (char *)SHA_final(&sha1_ctx);

    for (i = 0; i < SHA_DIGEST_SIZE; i++){
        sprintf((sha1_string+2*i),"%02x",sha1[i]);
    }
    *(sha1_string + 2*SHA_DIGEST_SIZE) = '\0';
    return 0;
}

/*this func is used to make hash table*/
static int str_hash(void* key)
{
    return hashmapHash(key, strlen((char*)key));
}

static bool str_icase_equals(void *KeyA, void *KeyB)
{
    return strcasecmp((char*)KeyA, (char*)KeyB) == 0;
}

static int read_ori_system_sha1(RecoveryUI* ui_,Hashmap** sha1_hash,FILE* file)
{

    char  buf[1024];
    ui = ui_;

    *sha1_hash = hashmapCreate(2048, str_hash, str_icase_equals);
    if(!*sha1_hash){
        ui->Print("hash map create fail\n");
        return -1;
    }

    while (fgets(buf,sizeof(buf),file) != NULL) {
        char app_name[512];
        char sha1_value[41];

        if (sscanf(buf,"%s %s",sha1_value,app_name) == 2) {
            char* app_name_dup = strdup(app_name);
            sha1_value[40] = '\0';
            char* sha1_value_dup = strdup(sha1_value);
            hashmapPut(*sha1_hash,app_name_dup,(void*)sha1_value_dup);
        }
    }

out:
    return hashmapSize(*sha1_hash);
}

/*
 * this func is used to read all of files stored in system partition recursively
 * all of the items is stored in hashmap new
 * the parameter is the path here is "/system/"
 *
 * the return value is the total num of items
*/
int read_dir(char *pathname, RecoveryUI* ui_, int* err_num)
{
    DIR * dir;
    struct dirent * ptr;
    char path[1024];
    char sys_info_name[1024];
    int count = 0;
    char buf[41];
    char* buf_fake="0000000000000000000000000000000000000000";
    char* buf_ori;
    int ret = -1;
    int check_ok_num = 0;
    bool need_new_checkbin = false;

    ui = ui_;

    dir =opendir(pathname);
    if (!dir) {
        ui->Print("open dir fail %s\n",pathname);
        goto out;
    }

    while((ptr = readdir(dir))!=NULL) {

        if (ptr->d_type == DT_DIR) {
            if (0 == strcmp(".",ptr->d_name) || 0 == strcmp("..",ptr->d_name)) {
                continue;
            }
            sprintf(path,"%s%s/",pathname,ptr->d_name);
            count += read_dir(path, ui, err_num);
        }
        else {
            sprintf(sys_info_name,"%s%s",pathname,ptr->d_name);
            ret = do_sha1(sys_info_name,ui,buf);
            need_new_checkbin = false;
            if(0 == strcmp(ptr->d_name, "recovery-resource.dat")) {
                count++;
                ui->Print("%s omit sha1 check!!! \n",ptr->d_name);
                continue;
            }
            if(0 == strcmp(ptr->d_name, "Camera2.apk")){
                continue;
            }

            if (hashmapContainsKey(app_to_sha1_ori, (void*)sys_info_name) ||
                (need_new_checkbin = true,app_to_sha1_ori_new && hashmapContainsKey(app_to_sha1_ori_new,(void*)sys_info_name))) {
                //ui->Print(" containeded %s ",ptr->d_name);
                if (!need_new_checkbin){
                    buf_ori = (char *)hashmapGet(app_to_sha1_ori,(void*)sys_info_name);
                }
                else {
                    buf_ori = (char *)hashmapGet(app_to_sha1_ori_new,(void*)sys_info_name);
                }

                if (strcasecmp(buf_ori,buf) == 0 || (ret && (strcasecmp(buf_ori,buf_fake) == 0))){
                //ui->Print("md5 value is  equaled!! ");
                //ui->Print(" check_ok_num is %d\n",++check_ok_num);
                    count++;
                    continue;
                }
                else {
                    if (app_to_sha1_ori_new && !need_new_checkbin) {
                        buf_ori = (char *)hashmapGet(app_to_sha1_ori_new,(void*)sys_info_name);
                        if (strcasecmp(buf_ori,buf) == 0 || (ret && (strcasecmp(buf_ori,buf_fake) == 0))) {
                            count++;
                            continue;
                        }
                    }

                    /* ignore some link errors begin */
                    if (strcasecmp(buf_ori,buf_fake) != 0) {
                        ui->Print("system check failed ori is %s ,now is %s ,sys name is %s!!! \n",buf_ori,buf,sys_info_name);
                        (*err_num)++;
                    }
                    else {
                        count++;
                        continue;
                    }
                    /* ignore some link errors end */
                }
            }
            else {
                ui->Print("system check failed ori is %s ,now is %s ,sys name is %s!!!!!! \n",app_to_sha1_ori, app_to_sha1_ori_new,sys_info_name);
                (*err_num)++;
            }
            count++;
        }
    }
    closedir(dir);
out:
    return count;
}

void
check_system_root(RecoveryUI* ui_)
{
    DIR* dir;
    int total_num = 0;
    int ori_total_num = 0;
    int ori_total_num_new = 0;
    int err_total_num = 0;
    struct dirent *ptr;
    char sha1_string[41];
    int ret;
    FILE* file;
    ui = ui_;
    // SPRD: add for checking system files
    ret = ensure_path_mounted("/systeminfo");
    if (ret) {
        ui->Print("systeminfo mount failed\n");
        goto out;
    }

    file = fopen("/systeminfo/check.bin","r");
    if (!file) {
        ui->Print("failed to open check.bin check failed %s \n", strerror(errno));
        goto out;
    } else {
        ui->Print("success to open check.bin \n");
    }

    ori_total_num = read_ori_system_sha1(ui, &app_to_sha1_ori, file);//create the hash table
    fclose(file);
    if (-1 == ori_total_num) {
        goto out;
    }

    file = fopen("/systeminfo/check.bin.new","r");
    if (file) {
        ui->Print("success to open check.bin.new \n");
        ori_total_num_new = read_ori_system_sha1(ui,&app_to_sha1_ori_new,file);//create the hash table
        fclose(file);
    } else {
        ui->Print("failed to open check.bin.new check failed %s \n", strerror(errno));
    }

    ui->Print("\nchecking NOW, please waiting...\n");
    total_num = read_dir("/system/",ui,&err_total_num);

    if ((0 == err_total_num) && ((ori_total_num == total_num) || (ori_total_num_new == total_num))) {
        ui->Print("\nsystem partition check Pass!\n");
    } else if (err_total_num) {
        ui->Print("\nsystem should have %d files, but now %d files.\n", ori_total_num, total_num);
    } else if (ori_total_num != total_num &&  ori_total_num_new != total_num) {
        ui->Print("\nsystem check failed the num of file under system should be %d  but now it is %d files.\n",ori_total_num,total_num);
    }
out:
    return;
}

extern "C" {
    int unmount_data_point(void);
}

int
main(int argc, char **argv) {
    time_t start = time(NULL);

    redirect_stdio(TEMPORARY_LOG_FILE);

    // If this binary is started with the single argument "--adbd",
    // instead of being the normal recovery binary, it turns into kind
    // of a stripped-down version of adbd that only supports the
    // 'sideload' command.  Note this must be a real argument, not
    // anything in the command file or bootloader control block; the
    // only way recovery should be run with this argument is when it
    // starts a copy of itself from the apply_from_adb() function.
    if (argc == 2 && strcmp(argv[1], "--adbd") == 0) {
        adb_main(0, DEFAULT_ADB_PORT);
        return 0;
    }

    printf("Starting recovery (pid %d) on %s", getpid(), ctime(&start));

    /* SPRD: cali boot mode we don't attach ubi device @{ */
    char tmp[PROPERTY_VALUE_MAX];

    property_get("ro.bootmode", tmp, "");

    if (0 == strcmp(tmp,"cali")) {
        return 0;
    } else{
        ubi_attach(0, "ubipac");
    }
    /* @} */

    load_volume_table();
    get_args(&argc, &argv);

    const char *send_intent = NULL;
    const char *update_package = NULL;
    bool should_wipe_data = false;
    bool should_wipe_cache = false;
    bool show_text = false;
    bool sideload = false;
    bool sideload_auto_reboot = false;
    bool just_exit = false;
    bool shutdown_after = false;
    int  check_root = 0;

    int arg;

    while ((arg = getopt_long(argc, argv, "", OPTIONS, NULL)) != -1) {
        switch (arg) {
        case 'i': send_intent = optarg; break;
        case 'u': update_package = optarg; break;
        case 'w': should_wipe_data = true; break;
        case 'c': should_wipe_cache = true; break;
        case 't': show_text = true; break;
        case 's': sideload = true; break;
        case 'a': sideload = true; sideload_auto_reboot = true; break;
        case 'x': just_exit = true; break;
        case 'l': locale = optarg; break;
        case 'g': {
            if (stage == NULL || *stage == '\0') {
                char buffer[20] = "1/";
                strncat(buffer, optarg, sizeof(buffer)-3);
                stage = strdup(buffer);
            }
            break;
        }
        case 'p': shutdown_after = true; break;
        case 'r': reason = optarg; break;
        case 'e': check_root = 1;break;
        case '?':
            LOGE("Invalid command argument\n");
            continue;
        }
    }

    if (locale == NULL) {
        load_locale_from_cache();
    }
    printf("locale is [%s]\n", locale);
    printf("stage is [%s]\n", stage);
    printf("reason is [%s]\n", reason);

    Device* device = make_device();
    ui = device->GetUI();
    gCurrentUI = ui;

    ui->SetLocale(locale);
    ui->Init();

    int st_cur, st_max;
    if (stage != NULL && sscanf(stage, "%d/%d", &st_cur, &st_max) == 2) {
        ui->SetStage(st_cur, st_max);
    }

    ui->SetBackground(RecoveryUI::NONE);
    if (show_text) ui->ShowText(true);

    struct selinux_opt seopts[] = {
      { SELABEL_OPT_PATH, "/file_contexts" }
    };

    sehandle = selabel_open(SELABEL_CTX_FILE, seopts, 1);

    if (!sehandle) {
        ui->Print("Warning: No file_contexts\n");
    }

    device->StartRecovery();

    printf("Command:");
    for (arg = 0; arg < argc; arg++) {
        printf(" \"%s\"", argv[arg]);
    }
    printf("\n");

    ui->Print("Unmount data point for remount: %d\n",
            unmount_data_point());

    if (update_package) {
        printf("enter convert path of update_package\n");
        /* SPRD: add fota support { */
        #ifdef FOTA_UPDATE_SUPPORT
          update_package = find_update_package(update_package);
          perform_fota = 1;
        #endif
        /* } */
        // For backwards compatibility on the cache partition only, if
        // we're given an old 'root' path "CACHE:foo", change it to
        // "/cache/foo".
        if (strncmp(update_package, "CACHE:", 6) == 0) {
            int len = strlen(update_package) + 10;
            char* modified_path = (char*)malloc(len);
            strlcpy(modified_path, "/cache/", len);
            strlcat(modified_path, update_package+6, len);
            printf("(replacing path \"%s\" with \"%s\")\n",
                   update_package, modified_path);
            update_package = modified_path;
        /* SPRD: update update_package contents @{ */
        }
        else if (strncmp(update_package, "DATA:", 5) == 0) {
            int len = strlen(update_package) + 10;
            char* modified_path = (char*)malloc(len);
            strlcpy(modified_path, "/data/", len);
            strlcat(modified_path, update_package+5, len);
            printf("(replacing path \"%s\" with \"%s\")\n",
                   update_package, modified_path);
            update_package = modified_path;
        }
        else if (strncmp(update_package, "SDCARD:", 7) == 0) {
            int len = strlen(update_package) + 12;
            char* modified_path = (char*)malloc(len);
            strlcpy(modified_path, SDCARD_ROOT, len);
            strlcat(modified_path, update_package+7, len);
            printf("(replacing path \"%s\" with \"%s\")\n",
                   update_package, modified_path);
            update_package = modified_path;
        }
        /* SPRD: add for covert path of otazip like "/storage/XXXX-XXXX/update.zip" to
           "/storage/sdcard0/update.zip" which is transeferd from setting @{ */
        else if (strncmp(update_package, "/storage/", 9) == 0) {
            int len = strlen(update_package) + 12;
            char* package_name = strrchr(update_package,'/');
            if (package_name == NULL){
                ui->Print("can't find the ota zip\n");
            }
            char* modified_path = (char*)malloc(len);
            strlcpy(modified_path, SDCARD_ROOT, len);
            strlcat(modified_path, package_name, len);
            printf("(replacing path \"%s\" with \"%s\")\n",
                   update_package, modified_path);
            update_package = modified_path;
        }
        /* @} */
        else if (strncmp(update_package, "/mnt/sdcard/", 12) == 0) {
            int len = strlen(update_package) + 12;
            char* modified_path = (char*)malloc(len);
            strlcpy(modified_path, SDCARD_ROOT, len);
            strlcat(modified_path, update_package+12, len);
            printf("(replacing path \"%s\" with \"%s\")\n",
                   update_package, modified_path);
            update_package = modified_path;
        }
        /* @} */
    }
    printf("\n");

    property_list(print_property, NULL);
    printf("\n");

    ui->Print("Supported API: %d\n", RECOVERY_API_VERSION);

    int status = INSTALL_SUCCESS;

    if (update_package != NULL) {
        fota_reset_status();
        err_no = 0;
        status = install_package(update_package, &should_wipe_cache, TEMPORARY_INSTALL_FILE, true, &err_no);
        if (status == INSTALL_SUCCESS && should_wipe_cache) {
            wipe_cache(false, device);
        }
        if (status != INSTALL_SUCCESS) {
			ui->SetBackground(RecoveryUI::INSTALL_FAILED);
			sleep(2);

            ui->Print("Installation aborted.\n");

            // If this is an eng or userdebug build, then automatically
            // turn the text display on if the script fails so the error
            // message is visible.
            if (is_ro_debuggable()) {
                ui->ShowText(true);
            }
		}else{
			ui->SetBackground(RecoveryUI::INSTALL_SUCESS);
			sleep(2);
		}
	/* SPRD: add fota support { */
        #ifdef FOTA_UPDATE_SUPPORT
          fota_update_install_finish(update_package, status);
        #endif
        /* } */
		write_result(status, err_no);
    } else if (should_wipe_data) {
        if (!wipe_data(false, device)) {
			ui->SetBackground(RecoveryUI::ERASING_FAILED);
			sleep(3);
            status = INSTALL_ERROR;
        }else{
			ui->SetBackground(RecoveryUI::ERASING_SUCESS);
			sleep(3);
		}
    } else if (should_wipe_cache) {
        if (!wipe_cache(false, device)) {
            status = INSTALL_ERROR;
        }
    } else if (sideload) {
        // 'adb reboot sideload' acts the same as user presses key combinations
        // to enter the sideload mode. When 'sideload-auto-reboot' is used, text
        // display will NOT be turned on by default. And it will reboot after
        // sideload finishes even if there are errors. Unless one turns on the
        // text display during the installation. This is to enable automated
        // testing.
        if (!sideload_auto_reboot) {
            ui->ShowText(true);
        }
        status = apply_from_adb(ui, &should_wipe_cache, TEMPORARY_INSTALL_FILE);
        if (status == INSTALL_SUCCESS && should_wipe_cache) {
            if (!wipe_cache(false, device)) {
                status = INSTALL_ERROR;
            }
        }
        ui->Print("\nInstall from ADB complete (status: %d).\n", status);
        if (sideload_auto_reboot) {
            ui->Print("Rebooting automatically.\n");
        }
    } else if (!just_exit) {
        status = INSTALL_NONE;  // No command specified
        ui->SetBackground(RecoveryUI::NO_COMMAND);

        // http://b/17489952
        // If this is an eng or userdebug build, automatically turn on the
        // text display if no command is specified.
   //     if (is_ro_debuggable()) {
            ui->ShowText(true);
    //    }
    }

    if (!sideload_auto_reboot && (status == INSTALL_ERROR || status == INSTALL_CORRUPT)) {
        copy_logs();
        //ui->SetBackground(RecoveryUI::ERROR);
    }

    Device::BuiltinAction after = shutdown_after ? Device::SHUTDOWN : Device::REBOOT;
    if ((status != INSTALL_SUCCESS && !sideload_auto_reboot) || ui->IsTextVisible()) {
        Device::BuiltinAction temp = prompt_and_wait(device, status);
        if (temp != Device::NO_ACTION) {
            after = temp;
        }
    }

    //SPRD add time info for format device
    printf("finish recovery \n");

    // Save logs and clean up before rebooting or shutting down.
    finish_recovery(send_intent);
    /* SPRD: add fota support { */
    #ifdef FOTA_UPDATE_SUPPORT
      if (perform_fota == 1) {
        finish_fota_update(update_package, TEMPORARY_LOG_FILE);
      }
    #endif
    /* } */

    switch (after) {
        case Device::SHUTDOWN:
            ui->Print("Shutting down...\n");
            property_set(ANDROID_RB_PROPERTY, "shutdown,");
            break;

        case Device::REBOOT_BOOTLOADER:
            ui->Print("Rebooting to bootloader...\n");
            property_set(ANDROID_RB_PROPERTY, "reboot,bootloader");
            break;

        default:
            ui->Print("Rebooting...\n");
            property_set(ANDROID_RB_PROPERTY, "reboot,");
            break;
    }
    sleep(5); // should reboot before this finishes
    return EXIT_SUCCESS;
}
