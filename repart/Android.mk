LOCAL_PATH:= $(call my-dir)
include $(CLEAR_VARS)

LOCAL_C_INCLUDES    +=  $(LOCAL_PATH) \
			$(LOCAL_PATH)/$(BOARD_PRODUCT_NAME)/

LOCAL_SRC_FILES:= \
        crc32.c \
        gptdata.c \
        main.c \

LOCAL_STATIC_LIBRARIES += libcutils libstdc++ libc
LOCAL_MODULE := repart
LOCAL_MODULE_TAGS := optional
LOCAL_FORCE_STATIC_EXECUTABLE := true
include $(BUILD_EXECUTABLE)

