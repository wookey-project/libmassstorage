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
#ifndef SCSI_H_
#define SCSI_H_

#include "usbmsc_framac_private.h"

#ifndef __FRAMAC__
typedef enum {
    SCSI_TRANSMIT_LINE_READY = 0,
    SCSI_TRANSMIT_LINE_BUSY,
    SCSI_TRANSMIT_LINE_ERROR,
} transmition_line_state_t;

typedef enum {
    SCSI_DIRECTION_IDLE = 0,
    SCSI_DIRECTION_SEND,
    SCSI_DIRECTION_RECV,
} transmission_direction_t;

typedef struct {
    uint8_t  direction;
    uint8_t  line_state;
    uint32_t size_to_process;
    uint32_t addr;
    uint32_t error;
    bool     queue_empty;
    uint8_t *global_buf;
    uint16_t global_buf_len;
    uint32_t block_size;
    uint32_t storage_size;
    uint8_t  state;
} scsi_context_t;

#endif/*!__FRAMAC__*/

scsi_context_t *scsi_get_context(void);

#endif/*!SCSI_H_*/
