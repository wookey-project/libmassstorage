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
#ifndef SCSI_RESP_H_
#define SCSI_RESP_H_

#include "libc/types.h"

/***************************
 * about responses
 *
 * SCSI responses are most of the time based on fixed content.
 * Although, there is cases where SCSI response length are dynamic
 * and are impacted by the associated SCSI command.
 *
 * The bellowing structures defined the supported SCSI responses,
 * for the above SCSI commands
 *
 **************************/

/* READ CAPACITY 10 PARAMETER DATA */
typedef struct __attribute__((packed)) {
    uint32_t ret_lba;
    uint32_t ret_block_length;
} read_capacity10_parameter_data_t;


/* READ CAPACITY 16 PARAMETER DATA */
typedef struct __attribute__((packed)) {
    uint64_t ret_lba;
    uint32_t ret_block_length;
    uint8_t reserved2:2;
    uint8_t rc_basis:2;
    uint8_t p_type:3;
    uint8_t prot_enable:1;
    uint8_t p_i_expornent:4;
    uint8_t logical_block_per_phys_block_component:4;
    uint16_t lbpme:1;
    uint16_t lbprz:1;
    uint16_t lowest_aligned_lba:14;
    uint8_t reserved1[16];
} read_capacity16_parameter_data_t;




/* REQUEST SENSE PARAMETER DATA */
typedef struct __packed request_sense_parameter_data {
    uint8_t error_code:7;
    uint8_t info_valid:1;
    uint8_t reserved1;
    uint8_t sense_key:4;
    uint8_t reserved:1;
    uint8_t ili:1;
    uint8_t eom:1;
    uint8_t filemark:1;
    uint8_t information[4];
    uint8_t additional_sense_length;
    uint32_t reserved8;
    uint8_t asc;
    uint8_t ascq;
    uint8_t field_replaceable_unit_code;
    uint8_t sense_key_specific[3];
} request_sense_parameter_data_t;


/* REPORT LUNS PARAMETER DATA */
typedef struct __attribute__((packed)) {
    uint32_t lun_list_length;
    uint32_t reserved;
    uint64_t luns[];
} report_luns_data_t;

/* READ FORMAT CAPACITIES response structure */
typedef struct __attribute__((packed)) {
    uint16_t reserved_1;
    uint8_t reserved_2;
    uint8_t capacity_list_length;
} capacity_list_header_t;

typedef enum {
    UNFORMATTED_MEDIA = 1,
    FORMATTED_MEDIA = 2,
    NO_CARTIDGE_IN_DRIVE = 3
} capacity_descriptor_code_t;

typedef struct __attribute__((packed)) {
    uint32_t number_of_blocks;
    uint8_t reserved:6;
    uint8_t descriptor_code:2;
    uint32_t block_length:24;
} curr_max_capacity_descriptor_t;

typedef struct __attribute__((packed)) {
    uint32_t number_of_blocks;
    uint8_t reserved;
    uint32_t block_length:24;
} formattable_capacity_descriptor_t;

typedef struct __attribute__((packed)) {
    capacity_list_header_t list_header;
    curr_max_capacity_descriptor_t cur_max_capacity;
    uint8_t num_format_descriptors;
    formattable_capacity_descriptor_t formattable_descriptor;
} capacity_list_t;

/* INQUIRY PARAMETER DATA */
typedef struct __packed inquiry_data {
    uint8_t periph_qualifier:3;
    uint8_t periph_device_type:5;
    uint8_t RMB:1;
    uint8_t reserved3:7;
    uint8_t version;
    uint8_t obsolete4:2;
    uint8_t NORMACA:1;
    uint8_t HISUP:1;
    uint8_t data_format:4;
    uint8_t additional_len;
    uint8_t SCCS:1;
    uint8_t ACC:1;
    uint8_t TPGS:2;
    uint8_t TPC:1;
    uint8_t reserved2:2;
    uint8_t PROTECT:1;
    uint8_t obsolete3:1;
    uint8_t ENCSERV:1;
    uint8_t VS2:1;
    uint8_t multip:1;
    uint8_t obsolete2:4;
    uint8_t obsolete1:6;
    uint8_t CMDQUE:1;
    uint8_t VS1:1;
    char    vendor_info[8];
    char    product_identification[16];
    char    product_revision[4];
    uint64_t drive_serial_number;
    uint8_t vendor_unique[12];
    uint8_t reserved1;
    uint16_t version_descriptor[8];
    /*reserved: bytes 74->95 */
    /* copyright notice: 96->n */

} inquiry_data_t;


/* About MODE SELECT and MODE SENSE responses   */

/* MODE SENSE PARAMETER DATA */

/*
 * MODE SELECT and MODE SENSE require a dynamic response content,
 * based on a data header (mode_parameter(6,10)_header_t, associated
 * with 0 or more mode parameters block descriptors.
 * This block descriptors are, among others, the following:
 * - short LBA mode
 * - long LBA mode
 * - Application tag
 * - background control mode
 * - background operation control mode
 * - Caching mode
 *  ... and so on ...
 *
 * This descriptors describe the way the SCSI client is able to
 * modify its way to communicate with the SCSI server, and the
 * various SCSI server capacities.
 */

/* First, we define the mode parameter headers, prefixing any block
 * descriptors that need to be sent
 */

/* For MODE SENSE(10) */
typedef struct __attribute__((packed)) {
    uint16_t mode_data_length;
    uint8_t medium_type;
    uint8_t WP:1;
    uint8_t reserved3:2;
    uint8_t DPOFUA:1;
    uint8_t reserved2:4;
    uint8_t reserved1:7;
    uint8_t longLBA:1;
    uint8_t reserved0;
    uint16_t block_descriptor_length;
} mode_parameter10_header_t;

/* For MODE SENSE(6) */
typedef struct __attribute__((packed)) {
    uint8_t mode_data_length;
    uint8_t medium_type;
    uint8_t WP:1;
    uint8_t reserved2:2;
    uint8_t DPOFUA:1;
    uint8_t reserved1:4;
    uint8_t block_descriptor_length;
} mode_parameter6_header_t;


/* MODE SELECT/MODE SENSE RESPONSE PARAMETERS */

/*
 * This part define the list of existing sense block descriptors that
 * can be sent back to MODE SENSE/MODE SELECT commands.
 */

typedef struct __attribute__((packed)) {
    uint32_t number_of_blocks;
    uint8_t reserved;
    uint32_t logical_block_length:24;
} mode_parameter_shortlba_t;

typedef struct __attribute__((packed)) {
    uint64_t number_of_blocks;
    uint32_t reserved;
    uint32_t logical_block_length;
} mode_parameter_longlba_t;


/* 1) Caching mode */
typedef struct __attribute__((packed)) {
    uint8_t PS:1;
    uint8_t SPF:1;
    uint8_t page_code:6;
    uint8_t page_length;
    uint8_t IC:1;
    uint8_t ABPF:1;
    uint8_t CAP:1;
    uint8_t disk:1;
    uint8_t size:1;
    uint8_t WCE:1;
    uint8_t MF:1;
    uint8_t RCD:1;
    uint8_t dmd_read_retention_prio:4;
    uint8_t write_retention_prio:4;
    uint16_t disable_prefetch_transfer_length;
    uint16_t min_prefetch;
    uint16_t max_prefetch;
    uint16_t max_prefetch_ceil;
    uint8_t FSW:1;
    uint8_t LB_CSS:1;
    uint8_t DRA:1;
    uint8_t vendor_specific:2;
    uint8_t SYNC_PROG:2;
    uint8_t NV_DIS:1;
    uint8_t cache_segment_number;
    uint16_t cache_segment_size;
    uint8_t reserved1;
} mode_parameter_caching_t;

/* TODO: the following is hard-coded as we reply only caching info.
 * A cleaner way, for MODE_SENSE and MODE_SELECT, would be to forge
 * the required mode pages and associated mode pages header depending
 * on the CDB content */
typedef struct __attribute__((packed)) {
    mode_parameter6_header_t header;

    // mode_parameter_caching_t  caching;
} mode_parameter6_data_t;

typedef struct __attribute__((packed)) {
    mode_parameter10_header_t header;

    // mode_parameter_caching_t  caching;
} mode_parameter10_data_t;

typedef union {
    mode_parameter6_data_t mode6;
    mode_parameter10_data_t mode10;
} u_mode_parameter;


/********* End of responses structures declaration ***********/

#endif /*!SCSI_RESP_H_ */
