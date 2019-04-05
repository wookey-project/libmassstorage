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
#ifndef SCSI_LOG_H_
#define SCSI_LOG_H_

#include "api/types.h"

/*
 * SCSI status, that are returned at each command terminaison
 */
typedef enum {
    SCSI_STATUS_GOOD                      = 0x00,
    SCSI_STATUS_CHECK_CONDITION           = 0x02,
    SCSI_STATUS_CONDITION_MET             = 0x04,
    SCSI_STATUS_BUSY                      = 0x08,
    SCSI_STATUS_INTERMEDIATE              = 0x10,
    SCSI_STATUS_INTERMEDIATE_CONFLICT_MET = 0x14,
    SCSI_STATUS_RESERVATION_CONFLICT      = 0x18,
    SCSI_STATUS_COMMAND_TERMINATED        = 0x22,
    SCSI_STATUS_TASK_SET_FULL             = 0x28,
    SCSI_STATUS_ACA_ACTIVE                = 0x30,
    SCSI_STATUS_TASK_ABORTED              = 0x40,
} scsi_status_t;

/*
 * Error informations management. All these sense informations are returned
 * in response to the MODE_SENSE command, using the saved error field. This
 * field hold the complete sense_key, ASC and ASCQ (if any) content.
 */

/*
 * SCSI sense key, defining the global error information
 */
typedef enum {
    SCSI_SENSE_NO_SENSE         = 0x0,
    SCSI_SENSE_RECOVERED_ERROR  = 0x1,
    SCSI_SENSE_NOT_READY        = 0x2,
    SCSI_SENSE_MEDIUM_ERROR     = 0x3,
    SCSI_SENSE_HARDWARE_ERROR   = 0x4,
    SCSI_SENSE_ILLEGAL_REQUEST  = 0x5,
    SCSI_SENSE_UNIT_ATTENTION   = 0x6,
    SCSI_SENSE_DATA_PROTECT     = 0x7,
    SCSI_SENSE_BLANK_CHECK      = 0x8,
    SCSI_SENSE_VENDOR_SPECIFIC  = 0x9,
    SCSI_SENSE_COPY_ABORTED     = 0xa,
    SCSI_SENSE_ABORTED_COMMAND  = 0xb,
    SCSI_SENSE_RESERVED         = 0xc,
    SCSI_SENSE_VOLUME_OVERFLOW  = 0xd,
    SCSI_SENSE_MISCOMPARE       = 0xe,
    SCSI_SENSE_COMPLETED        = 0xf,
} scsi_sense_key_t;

/*
 * TODO: complete Additional Sense and Additional Sense Qualifier codes,
 * defining more precise error informations.
 * Although, these lists are *huge*. Here we use a define as the enumerate
 * is incomplete
 */
# define ASC_NO_ADDITIONAL_SENSE                    0x00
# define ASC_LOGICAL_BLOCK_ADDRESS_OUT_OF_RANGE     0x21
# define ASC_MEDIUM_NOT_PRESENT                     0x3a
# define ASC_PERIPHERAL_DEVICE_WRITE_FAULT          0x03
# define ASC_UNRECOVERED_READ_ERROR                 0x11
# define ASC_WRITE_PROTECTED                        0x27
# define ASC_WRITE_ERROR                            0x0C
# define ASC_SERVO_FAULT                            0x09
# define ASC_ABORTED_COMMAND                        0x0B
# define ASC_ECHO_BUFFER_OVERWRITTEN                0x3F

# define ASCQ_NO_ADDITIONAL_SENSE                   0x00
# define ASCQ_LOGICAL_BLOCK_ADDRESS_OUT_OF_RANGE    0x00
# define ASCQ_MEDIUM_NOT_PRESENT                    0x00
# define ASCQ_PERIPHERAL_DEVICE_WRITE_FAULT         0x00
# define ASCQ_UNRECOVERED_READ_ERROR                0x00
# define ASCQ_WRITE_PROTECTED                       0x00

/* SCSI errors */
static inline scsi_sense_key_t scsi_error_get_sense_key(uint32_t error) {
    return (scsi_sense_key_t)((error & 0xf0000) >> 16);
}

static inline uint8_t scsi_error_get_asc(uint32_t error) {
    return (uint8_t)((error & 0xff00) >> 8);
}

static inline uint8_t scsi_error_get_ascq(uint32_t error) {
    return (uint8_t)(error & 0xff);
}

#endif
