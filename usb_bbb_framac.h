/*
 *
 * Copyright 2018 The wookey project team <wookey@ssi.gouv.fr>
 *   - Ryad     Benadjila
 *   - Arnauld  Michelizza
 *   - Mathieu  Renard
 *   - Philippe Thierry
 *   - Philippe Trebuchet
 *
 * This package is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * ur option) any later version.
 *
 * This package is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
 * PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this package; if not, write to the Free Software Foundation, Inc., 51
 * Franklin St, Fifth Floor, Boston, MA 02110-1301 USA
 *
 */
#ifndef USB_BBB_FRAMAC_H
#define USB_BBB_FRAMAC_H

#include "libc/types.h"

#ifdef __FRAMAC__
mbed_error_t usb_bbb_data_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep __attribute__((unused)));

mbed_error_t usb_bbb_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep __attribute__((unused)));

typedef enum bbb_state {
    USB_BBB_STATE_READY,
    USB_BBB_STATE_CMD,
    USB_BBB_STATE_DATA,
    USB_BBB_STATE_STATUS,
} usb_bbb_state_t;

typedef void (*usb_bbb_cb_cmd_received_t)(uint8_t cdb[], uint8_t cdb_len);
typedef void (*usb_usb_cb_data_received_t)(uint32_t size);
typedef void (*usb_usb_cb_data_sent_t)(void);

/*
 * This is the overall BBB context, set at initialization time.
 */
typedef struct {
    uint8_t                     state;
    usbctrl_interface_t         iface;
    usb_bbb_cb_cmd_received_t   cb_cmd_received;
    usb_usb_cb_data_received_t  cb_data_received;
    usb_usb_cb_data_sent_t      cb_data_sent;
    uint32_t                    tag;
} usb_bbb_context_t;


static usb_bbb_context_t bbb_ctx = {
    .state = USB_BBB_STATE_READY,
    .iface = { 0 },
    .cb_cmd_received = NULL,
    .cb_data_received = NULL,
    .cb_data_sent = NULL,
    .tag = 0
};



#define USB_BBB_CBW_SIG		0x43425355      /* "USBC" */

/* Command Block Wrapper exported for FramaC driver ISR emulation */
struct __packed scsi_cbw {
    uint32_t sig;
    uint32_t tag;
    uint32_t transfer_len;
    struct {
        uint8_t reserved:7;
        uint8_t direction:1;
    } flags;
    struct {
        uint8_t lun:4;
        uint8_t reserved:4;
    } lun;
    struct {
        uint8_t cdb_len:5;
        uint8_t reserved:3;
    } cdb_len;
    uint8_t cdb[16];            // FIXME We must handle CDB6 CDB10 CDB12 CDB16 ?
};

struct scsi_cbw cbw;
#endif




#endif/*USB_BBB_FRAMAC_H*/
