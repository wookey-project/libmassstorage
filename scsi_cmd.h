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
#ifndef SCSI_CMD_H_
#define SCSI_CMD_H_


/* SCSI commands list */
typedef enum {
    SCSI_CMD_FORMAT_UNIT = 0x04,        // Mandatory
    SCSI_CMD_INQUIRY = 0x12,    // Mandatory
    SCSI_CMD_MODE_SELECT_6 = 0x15,
    SCSI_CMD_MODE_SELECT_10 = 0x55,
    SCSI_CMD_MODE_SENSE_10 = 0x5a,      // Requiered for some bootable devices
    SCSI_CMD_MODE_SENSE_6 = 0x1a,       // Requiered for some bootable devices
    SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL = 0x1e,
    SCSI_CMD_READ_6 = 0x08,     // Mandatory for olders
    SCSI_CMD_READ_10 = 0x28,    // Mandatory
    SCSI_CMD_READ_CAPACITY_10 = 0x25,   // Mandatory
    SCSI_CMD_READ_FORMAT_CAPACITIES = 0x23,
    SCSI_CMD_REPORT_LUNS = 0xa0,        // Mandatory
    SCSI_CMD_REQUEST_SENSE = 0x03,      // Mandatory
    SCSI_CMD_SEND_DIAGNOSTIC = 0x1d,    // Mandatory
    SCSI_CMD_START_STOP_UNIT = 0x1b,
    SCSI_CMD_SYNCHRONIZE_CACHE_10 = 0x35,
    SCSI_CMD_TEST_UNIT_READY = 0x00,    // Mandatory
    SCSI_CMD_VERIFY_10 = 0x2f,
    SCSI_CMD_WRITE_6 = 0x0a,    // Mandatory for olders
    SCSI_CMD_WRITE_10 = 0x2a,   // Mandatory
    SCSI_CMD_READ_CAPACITY_16 = 0x9e,
} scsi_operation_code_t;

/***************************
 * about SCSI commands
 *
 * All commands here are defined as packed structure
 * *without* the starting operation byte.
 *
 * All commands start with the same field (the operation byte)
 * which is used to segregate commands.
 *
 * This byte is added to the cdb_t structure, associating
 * this byte to an union associating all supported commands
 * (see bellow)
 **************************/

/* MODE SENSE 10  */
typedef struct __attribute__((packed)) {
    uint8_t reserved1:3;
    uint8_t LLBAA:2;
    uint8_t DBD:2;
    uint8_t reserved2:1;
    uint8_t PC:2;
    uint8_t page_code:6;
    uint8_t sub_page_code;
    uint16_t reserved3;
    uint16_t allocation_length;
    uint8_t control;
} cdb10_mode_sense_t;


/* PREVENT ALLOW REMOVAL */
typedef struct __attribute__((packed)) {
    uint16_t reserved1;
    uint8_t reserved2:6;
    uint8_t prevent:2;
    uint8_t control;
} cdb10_prevent_allow_removal_t;

/* REQUEST SENSE 10 */
typedef struct __attribute__((packed)) {
    uint8_t reserved1:7;
    uint8_t desc:1;
    uint16_t reserved;
    uint8_t allocation_length;
} cdb10_request_sense_t;

/* READ FORMAT CAPACITIES */
typedef struct __attribute__((packed)) {
    uint8_t lun:3;
    uint8_t reserved_1:5;
    uint32_t reserved_2;
    uint8_t reserved_3;
    uint8_t allocation_length_msb;
    uint8_t allocation_length_lsb;
    uint16_t reserved_4;
    uint8_t reserved_5;
} cdb12_read_format_capacities_t;

/* READ 6 / WRITE 6 */
typedef struct __attribute__((packed)) {
    uint32_t reserved:3;
    uint32_t logical_block:21;
    uint8_t transfer_blocks;
    uint8_t control;
} cdb6_t;


/* READ 10 / WRITE 10 */
typedef struct __attribute__((packed)) {
    uint8_t misc1:3;
    uint8_t service_action:5;
    uint32_t logical_block;
    uint8_t misc2;
    uint16_t transfer_blocks;
    uint8_t control;
} cdb10_t;

/* MODE SENSE 6 */
typedef struct __attribute__((packed)) {
    uint8_t LUN:3;
    uint8_t reserved4:1;
    uint8_t DBD:1;
    uint8_t reserved3:3;
    uint8_t PC:2;
    uint8_t page_code:6;
    uint8_t reserved2;
    uint8_t allocation_length;
    uint8_t vendor_specific:2;
    uint8_t reserved1:4;
    uint8_t flag:1;
    uint8_t link:1;
} cdb6_mode_sense_t;

/* MODE SELECT 6 */
typedef struct __attribute__((packed)) {
    uint8_t reserved3:3;
    uint8_t PF:1;
    uint8_t reserved2:2;
    uint8_t RTD:1;
    uint8_t SP:1;
    uint16_t reserved1;
    uint8_t parameter_list_length;
    uint8_t control;
} cdb6_mode_select_t;


/* INQUIRY 6 */
typedef struct __attribute__((packed)) {
    uint8_t reserved:6;
    uint8_t CMDDT:1;            /* obsolete */
    uint8_t EVPD:1;
    uint8_t page_code;
    uint16_t allocation_length;
    uint8_t control;
} cdb6_inquiry_t;

/* MODE SELECT 10 */
typedef struct __attribute__((packed)) {
    uint8_t reserved3:3;
    uint8_t PF:1;
    uint8_t reserved2:3;
    uint8_t SP:1;
    uint8_t reserved1_bis;
    uint32_t reserved1;
    uint16_t parameter_list_length;
    uint8_t control;
} cdb10_mode_select_t;

/* REPORT LUNS */
typedef struct __attribute__((packed)) {
    uint8_t reserved3;
    uint8_t selected_report;
    uint16_t reserved2_2;
    uint8_t reserved2_1;
    uint32_t allocation_length;
    uint8_t reserved1;
    uint8_t control;
} cdb12_report_luns_t;


/* READ CAPACITY 16 */
typedef struct __attribute__((packed)) {
    uint8_t Reserved2:3;
    uint8_t service_action:5;
    uint64_t logical_block_address;
    uint32_t allocation_length;
    uint8_t Reserved1:7;
    uint8_t PMI:1;
    uint8_t control;
} cdb16_read_capacity_16_t;

/*
 * polymorphic SCSI command content, using a C union
 * type.
 * Each command is identified by an operation attribute before
 * the command content used as segregation field:
 *
 * [cmd id][type-variable, length variable cmd content]
 */
typedef union {
    /* CDB 6 bytes length */
    cdb6_t  cdb6;               /* read and write */
    cdb6_mode_sense_t cdb6_mode_sense;
    cdb6_mode_select_t cdb6_mode_select;
    cdb6_inquiry_t cdb6_inquiry;
    /* CDB 10 bytes length */
    cdb10_t cdb10;              /* read and write */
    cdb10_mode_sense_t cdb10_mode_sense;
    cdb10_mode_select_t cdb10_mode_select;
    cdb10_prevent_allow_removal_t cdb10_prevent_allow_removal;
    cdb10_request_sense_t cdb10_request_sense;
    /* CDB 12 bytes length */
    cdb12_report_luns_t cdb12_report_luns;
    cdb12_read_format_capacities_t cdb12_read_format_capacities;
    /* CDB 16 bytes length */
    cdb16_read_capacity_16_t cdb16_read_capacity;
} u_cdb_payload;

/*
 * SCSI command storage area, associating the operation byte
 * and the union field in a packed content
 */
typedef struct __attribute__((packed)) {
    uint8_t operation;
    u_cdb_payload payload;
} cdb_t;



#endif /*!SCSI_CMD_H_ */
