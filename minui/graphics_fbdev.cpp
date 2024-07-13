/*
 * Copyright (C) 2014 The Android Open Source Project
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

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <fcntl.h>
#include <stdio.h>

#include <sys/cdefs.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/types.h>

#include <linux/fb.h>
#include <linux/kd.h>

#include "minui.h"
#include "graphics.h"

/* SPRD: add for support rotate @{ */
#include <utils/Log.h>
//#include <cutils/properties.h>
#include "cutils/properties.h"
/* @} */
static GRSurface* fbdev_init(minui_backend*);
static void fbdev_sync(GRSurface*);
static GRSurface* fbdev_flip(minui_backend*);
static void fbdev_blank(minui_backend*, bool);
static void fbdev_exit(minui_backend*);

static GRSurface gr_framebuffer[3];
static bool double_buffered;
static bool three_buffered;
static GRSurface* gr_draw = NULL;
static int displayed_buffer;

static fb_var_screeninfo vi;
static int fb_fd = -1;

static minui_backend my_backend = {
    .init = fbdev_init,
    .sync = fbdev_sync,
    .flip = fbdev_flip,
    .blank = fbdev_blank,
    .exit = fbdev_exit,
};

/* SPRD: add for support rotate @{ */
static int rotation = FB_ROTATE_UR;
static GRSurface *gr_temp;
/* @} */

minui_backend* open_fbdev() {
    return &my_backend;
}

static void fbdev_blank(minui_backend* backend __unused, bool blank)
{
    int ret;

    ret = ioctl(fb_fd, FBIOBLANK, blank ? FB_BLANK_POWERDOWN : FB_BLANK_UNBLANK);
    if (ret < 0)
        perror("ioctl(): blank");
}
static void set_displayed_framebuffer(unsigned n)
{
    if (n > 2 || !(three_buffered || double_buffered)) return;
    if (n > 1 && !three_buffered ) return;
 /*SPRD remove temporary,cause it due to the result of cannot enter recovery ui @{*/
    //SPRD:remove
    //vi.yres_virtual = gr_framebuffer[0].height * 2;
 /* @}*/
    vi.yoffset = n * gr_framebuffer[0].height;
    vi.bits_per_pixel = gr_framebuffer[0].pixel_bytes * 8;
    if (ioctl(fb_fd, FBIOPUT_VSCREENINFO, &vi) < 0) {
        perror("active fb swap failed");
    }
    displayed_buffer = n;
}

static GRSurface* fbdev_init(minui_backend* backend) {
    int fd = open("/dev/graphics/fb0", O_RDWR);
    if (fd == -1) {
        perror("cannot open fb0");
        return NULL;
    }

    fb_fix_screeninfo fi;
    if (ioctl(fd, FBIOGET_FSCREENINFO, &fi) < 0) {
        perror("failed to get fb0 info");
        close(fd);
        return NULL;
    }

    if (ioctl(fd, FBIOGET_VSCREENINFO, &vi) < 0) {
        perror("failed to get fb0 info");
        close(fd);
        return NULL;
    }

    // We print this out for informational purposes only, but
    // throughout we assume that the framebuffer device uses an RGBX
    // pixel format.  This is the case for every development device I
    // have access to.  For some of those devices (eg, hammerhead aka
    // Nexus 5), FBIOGET_VSCREENINFO *reports* that it wants a
    // different format (XBGR) but actually produces the correct
    // results on the display when you write RGBX.
    //
    // If you have a device that actually *needs* another pixel format
    // (ie, BGRX, or 565), patches welcome...

    printf("fb0 reports (possibly inaccurate):\n"
           "  vi.bits_per_pixel = %d\n"
           "  vi.red.offset   = %3d   .length = %3d\n"
           "  vi.green.offset = %3d   .length = %3d\n"
           "  vi.blue.offset  = %3d   .length = %3d\n",
           vi.bits_per_pixel,
           vi.red.offset, vi.red.length,
           vi.green.offset, vi.green.length,
           vi.blue.offset, vi.blue.length);

    void* bits = mmap(0, fi.smem_len, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (bits == MAP_FAILED) {
        perror("failed to mmap framebuffer");
        close(fd);
        return NULL;
    }

    memset(bits, 0, fi.smem_len);

    /* SPRD: add for support rotate @{ */
    char rotate_str[PROPERTY_VALUE_MAX+1];
    property_get("ro.sf.hwrotation", rotate_str, "0");
    printf("in %s: ro.sf.hwrotation=%s\n",__func__,rotate_str);
    if (!strcmp(rotate_str, "90")) {
        rotation = FB_ROTATE_CW;
    } else if (!strcmp(rotate_str, "180")) {
        rotation = FB_ROTATE_UD;
    } else if (!strcmp(rotate_str, "270")) {
        rotation = FB_ROTATE_CCW;
    }
    /* @} */

    printf("fb0 reports (possibly inaccurate):\n"
           "  fi.line_length = %3d\n"
           "  vi.xres   = %3d    vi.yres = %3d\n",
           fi.line_length,
           vi.xres, vi.yres);
    gr_framebuffer[0].width = vi.xres;
    gr_framebuffer[0].height = vi.yres;
    gr_framebuffer[0].row_bytes = fi.line_length;
    gr_framebuffer[0].pixel_bytes = vi.bits_per_pixel / 8;
    gr_framebuffer[0].data = reinterpret_cast<uint8_t*>(bits);
    memset(gr_framebuffer[0].data, 0, gr_framebuffer[0].height * gr_framebuffer[0].row_bytes);

    /* check if we can use double buffering */
    if (vi.yres * fi.line_length * 2 <= fi.smem_len) {
        double_buffered = true;
	three_buffered = false;
        memcpy(gr_framebuffer+1, gr_framebuffer, sizeof(GRSurface));
        gr_framebuffer[1].data = gr_framebuffer[0].data +
            gr_framebuffer[0].height * gr_framebuffer[0].row_bytes;
		
        if (vi.yres * fi.line_length * 3 <= fi.smem_len) {
            double_buffered = false;
            three_buffered = true;
            memcpy(gr_framebuffer+2, gr_framebuffer, sizeof(GRSurface));
            gr_framebuffer[2].data = gr_framebuffer[0].data +
                2 * gr_framebuffer[0].height * gr_framebuffer[0].row_bytes;
        }

        /* SPRD: add for support rotate @{
         * @orig
        gr_draw = gr_framebuffer+1;
         */
        if (rotation == FB_ROTATE_UR) {
            gr_draw = gr_framebuffer+( double_buffered ? 1 : 2 );
        } else {
            gr_temp = (GRSurface *) malloc(sizeof( GRSurface));
            if((vi.rotate ^ rotation) & 1) {
                gr_temp->width = vi.yres;
                gr_temp->height = vi.xres;
                gr_temp->row_bytes = vi.yres * vi.bits_per_pixel / 8;
            } else {
                gr_temp->width = vi.xres;
                gr_temp->height = vi.yres;
                gr_temp->row_bytes = fi.line_length;
            }
            gr_temp->pixel_bytes = vi.bits_per_pixel / 8;
            gr_temp->data = (unsigned char*) malloc(gr_temp->height * gr_temp->row_bytes);
            gr_draw = gr_temp;
        }
        /* @} */

    } else {
        double_buffered = false;
	three_buffered = false;
        // Without double-buffering, we allocate RAM for a buffer to
        // draw in, and then "flipping" the buffer consists of a
        // memcpy from the buffer we allocated to the framebuffer.

        gr_draw = (GRSurface*) malloc(sizeof(GRSurface));
        memcpy(gr_draw, gr_framebuffer, sizeof(GRSurface));
        gr_draw->data = (unsigned char*) malloc(gr_draw->height * gr_draw->row_bytes);
        if (!gr_draw->data) {
            perror("failed to allocate in-memory surface");
            return NULL;
        }
    }

    memset(gr_draw->data, 0, gr_draw->height * gr_draw->row_bytes);
    fb_fd = fd;
    set_displayed_framebuffer(0);

    printf("framebuffer: %d (%d x %d)\n", fb_fd, gr_draw->width, gr_draw->height);

    fbdev_blank(backend, true);
    fbdev_blank(backend, false);

    return gr_draw;
}

/* SPRD: add for support rotate @{ */
void gr_rotate(GRSurface *dst_surface, GRSurface *src_surface)
{
    unsigned int  i,j;
    unsigned int width, height;
    /* copy data from the in-memory surface to the buffer we're about
     * to make active. */
    i = vi.xres * vi.yres;

    //printf("entry %s:rotation=%d\n",__func__,rotation);
    width = src_surface->width;
    height = src_surface->height;

    if (vi.bits_per_pixel == 16) {
        unsigned short *out, *in;

        out = (unsigned short *)dst_surface->data;
        in = (unsigned short *)src_surface->data;

        if (rotation == FB_ROTATE_UD) { //180
            unsigned int size = width * height;
            out += size - 1;

            for (i = size; i--; )
                *out-- = *in++;
        } else if (rotation == FB_ROTATE_CW) { //90
            unsigned int h = height - 1;
            for (i = 0; i < height; i++)
                for (j = 0; j < width; j++)
                    out[height * j + h - i] = *in++;
        } else if (rotation == FB_ROTATE_CCW) { //270
            int w = width - 1;
            for (i = 0; i < height; i++)
                for (j = 0; j < width; j++)
                    out[height * (w - j) + i] = *in++;
        } else if (rotation == FB_ROTATE_UR) {
            memcpy(out, in, width * height * 2);
        }

    } else {
        unsigned int *out, *in;

        out = (unsigned int *)dst_surface->data;
        in = (unsigned int *)src_surface->data;

        if (rotation == FB_ROTATE_UD) { //180
            unsigned int size = width * height;
            out += size - 1;

            for (i = size; i--; )
                *out-- = *in++;
        } else if (rotation == FB_ROTATE_CW) { //90
            unsigned int h = height - 1;
            for (i = 0; i < height; i++)
                for (j = 0; j < width; j++)
                    out[height * j + h - i] = *in++;
        } else if (rotation == FB_ROTATE_CCW) { //270
            int w = width - 1;
            for (i = 0; i < height; i++)
                for (j = 0; j < width; j++)
                    out[height * (w - j) + i] = *in++;
        } else if (rotation == FB_ROTATE_UR) {
            memcpy(out, in, width * height * 4);
        }
    }
}
/* @} */

static void fbdev_sync(GRSurface* draw __unused)
{
        if (ioctl(fb_fd, FBIO_WAITFORVSYNC, &vi) < 0)
        {
          printf("sync fb failed\n");
        }
}

static GRSurface* fbdev_flip(minui_backend* backend __unused) {
    if (double_buffered || three_buffered) {
#if defined(RECOVERY_BGRA)
/* SPRD: modified for transform BGRA to RGB565 @{ */
#ifndef LCD_FORMAT_RGB565
        // In case of BGRA, do some byte swapping
        unsigned int idx;
        unsigned char tmp;
        unsigned char* ucfb_vaddr = (unsigned char*)gr_draw->data;
        for (idx = 0 ; idx < (gr_draw->height * gr_draw->row_bytes);
                idx += 4) {
            tmp = ucfb_vaddr[idx];
            ucfb_vaddr[idx    ] = ucfb_vaddr[idx + 2];
            ucfb_vaddr[idx + 2] = tmp;
        }
#endif
/* @} */
#endif
        // Change gr_draw to point to the buffer currently displayed,
        // then flip the driver so we're displaying the other buffer
        // instead.
        /* SPRD: add for support rotate @{
         * @orig
        gr_draw = gr_framebuffer + displayed_buffer;
         */
        if (rotation == FB_ROTATE_UR) {
            gr_draw = gr_framebuffer + (double_buffered ? displayed_buffer : (displayed_buffer + 1) % 3 );
        } else {
            gr_rotate(&gr_framebuffer[double_buffered ? (1 - displayed_buffer) : (displayed_buffer + 1) % 3], gr_temp);
        }
        /* @} */
        set_displayed_framebuffer( double_buffered ? (1 - displayed_buffer) : (displayed_buffer + 2) % 3);
    } else {
        // Copy from the in-memory surface to the framebuffer.
        memcpy(gr_framebuffer[0].data, gr_draw->data,
               gr_draw->height * gr_draw->row_bytes);
    }
    return gr_draw;
}

static void fbdev_exit(minui_backend* backend __unused) {
    close(fb_fd);
    fb_fd = -1;

    if (!(double_buffered || three_buffered) && gr_draw) {
        free(gr_draw->data);
        free(gr_draw);
    }
    /* SPRD: add for support rotate @{ */
   if (rotation != FB_ROTATE_UR && (double_buffered || three_buffered )) {
        free(gr_temp->data);
        free(gr_temp);
    }
    /* @} */
    gr_draw = NULL;
}
