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
#ifndef USB_BBB_H
#define USB_BBB_H

#include "libc/regutils.h"
#include "libusbctrl.h"


#ifndef __FRAMAC__
#define BBB_IN_EP 1
#define BBB_OUT_EP 2
#endif

typedef void (*usb_bbb_cb_cmd_received_t)(uint8_t *cdb, uint8_t cdb_len);
typedef void (*usb_bbb_cb_data_received_t)(uint32_t size);
typedef void (*usb_bbb_cb_data_sent_t)(void);



/**
 * usb_bbb_init - Initialize the bulk only layer
 * @cmd_received: callback called when a command is received. Parameters are the
 * command block and its size.
 * @data_received: callback called when data is received. The parameter is the
 * size of received data.
 * @data_sent: callback called when data has been sent
 */
mbed_error_t usb_bbb_configure(uint32_t usbdci_handler);

void usb_bbb_reconfigure(void);

void usb_bbb_declare(usb_bbb_cb_cmd_received_t cmd_received,
                     usb_bbb_cb_data_received_t data_received,
                     usb_bbb_cb_data_sent_t data_sent);

enum csw_status {
    CSW_STATUS_SUCCESS = 0,
    CSW_STATUS_FAILED = 1,
    CSW_STATUS_ERROR = 2        /* host should send reset */
};

/**
 * usb_bbb_send_csw - Send the status of the command
 * @src: address of the data to send. The buffer's size must be at list @size.
 * @data_residue: number of bytes not sent nor received.
 */
void    usb_bbb_send_csw(enum csw_status status, uint32_t data_residue);

/**
 * usb_bbb_send - Send data throw USB layer
 * @src: address of the data to send. The buffer's size must be at least @size.
 * @size: number of bytes to send.
 * @ep: endpoint on which send data.
 */
void    usb_bbb_send(const uint8_t * src, uint32_t size);

/**
 * usb_bbb_read - Read data from USB layer
 * @dst: buffer in which read data will be written.
 * @size: number of bytes to read.
 * @ep: endpoint on which read data.
 */
void    usb_bbb_recv(uint8_t *dst, uint32_t size);

void    read_next_cmd(void);

#endif /* USB_BBB_H */
