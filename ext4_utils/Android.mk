# Copyright 2010 The Android Open Source Project

LOCAL_PATH:= $(call my-dir)

libext4_utils_src_files := \
    make_ext4fs.c \
    ext4fixup.c \
    ext4_utils.c \
    allocate.c \
    contents.c \
    extent.c \
    indirect.c \
    sha1.c \
    wipe.c \
    crc16.c \
    ext4_sb.c


libext4_utils_src_files += \
    key_control.cpp \
    ext4_crypt.cpp \
    unencrypted_properties.cpp


include $(CLEAR_VARS)
LOCAL_SRC_FILES := $(libext4_utils_src_files) \
    ext4_crypt_init_extensions.cpp
LOCAL_MODULE := libext4_utils_static_ota
LOCAL_STATIC_LIBRARIES := \
    libsparse_static
include $(BUILD_STATIC_LIBRARY)

