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
#ifndef USBMSC_FRAMAC_PRIVATE_H_
#define USBMSC_FRAMAC_PRIVATE_H_
#include "libc/types.h"
#include "libusbotghs.h"

#ifdef __FRAMAC__
/*
 * INFO:
 * For the sake of ACSL annotations, some private types, local variables & structures have to be visible from various
 * parts of the library. This permit to precisely set all the border effects of each function, ensuring the noRTE
 * property in Typed+Ref (sound) memory model.
 * When compiled in non-framaC mode, all static globals, local types are keeped in their original places.
 */

/* 1. About BBB */

#define BBB_IN_EP 1
#define BBB_OUT_EP 2

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


usb_bbb_context_t bbb_ctx = {
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

struct scsi_cbw *usb_bbb_get_cbw(void);

/* 2. About SCSI */

/* moved state definition here to allow ACSL usage in assigns */
typedef enum scsi_state {
    SCSI_IDLE  = 0x0,
    SCSI_ERROR = 0x1,
} scsi_state_t;


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

/* here we need to access scsi_ctx in ACSL content of entrypoint.c to assert its
 * state at various point. To do that, in FRAMAC mode only, we move the global and
 * its definition from the scsi.c to the scsi.h file. In non-framaC case, this global
 * is keeped in scsi.c */
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


scsi_context_t scsi_ctx;

cdb_t queued_cdb = { 0 };

/* INFO: this variable is usually an application-scope variable, instead of libMSC local one. Although, for the FramaC sake of globals check, it has been set here, to be seen correclty from
 * both scsi and bbb scopes, as framaC doesn't handle link-level resolution of variable address */
bool reset_requested = false;

void scsi_data_sent(void);

void scsi_data_available(uint32_t size);

void scsi_parse_cdb(uint8_t cdb[], uint8_t cdb_len);

/* FramaC specific */
scsi_context_t *scsi_get_context(void);

void scsi_error(uint16_t sensekey, uint8_t asc, uint8_t ascq);


/**************************************************************
 * FramaC specific substitution APIs, predicates and functions
 */

/*********************************
 * 1. Predicates
 */

/*@
  // INFO: We assumes that framaC is targetting x86-32 architecture (i.e. little indian architecture, for which
  // htons() requires bytes inversion.
  predicate is_invalid_inquiry(cdb6_inquiry_t *inq) =
    ((inq->EVPD == 0) && ((((inq->allocation_length & 0xff) << 8) | (inq->allocation_length >> 8)) < 5)) ||
    ((inq->EVPD == 1) && ((((inq->allocation_length & 0xff) << 8) | (inq->allocation_length >> 8)) < 4));


  // INFO: We assumes that framaC is targetting x86-32 architecture (i.e. little indian architecture, for which
  // ntohl() requires bytes inversion.
  predicate is_invalid_report_luns(cdb12_report_luns_t *rl) =
                        (((rl->allocation_length & 0xff)   << 24)    |
                         ((rl->allocation_length & 0xff00) << 8)     |
                         ((rl->allocation_length & 0xff0000) >> 8)   |
                         ((rl->allocation_length & 0xff000000) >> 24)) < 16;

 */


/*********************************
 * 2. Substitutions
 */

/*
 * INFO:
 * In scsi.c file, all usage of memcpy are based on u8* arrays recopy.
 * Instead of writing explicit loop in each function, we implement a local memcpy_u8 function.
 * This function requires all its input arguments to be valid.
 *
 * This substitution of memcpy should be removed as soon as the instantiate plugin is working
 * with the -nostdlib use case.
 */
/*@
  @ requires len > 0;
  @ requires \valid(dst+(0..len-1));
  @ requires \valid_read(src+(0..len-1));
  @ requires \separated(dst+(0..len-1),src+(0..len-1));
  @ assigns *(dst+(0..len-1));
  */
inline void FC_memcpy_u8(uint8_t *dst, uint8_t const *src, uint8_t len)
{
    /*@
      @ loop invariant 0 <= i <= len;
      @ loop assigns i, dst[0..len-1];
      @ loop variant len - i;
      */
    for (uint8_t i = 0; i < len; ++i) {
        dst[i] = src[i];
        /*@ assert dst[i] == src[i]; */
    }
    /* loops make wp forgetting everything. Let's help it... */
    return;
}

/*@
  @ requires len > 0;
  @ requires \valid(dst+(0..len-1));
  @ requires \valid_read(src+(0..len-1));
  @ requires \separated(dst+(0..len-1),src+(0..len-1));
  @ assigns *(dst+(0..len-1));
  */
inline void FC_memcpy_ch(char *dst, char const *src, uint8_t len)
{

    /*@
      @ loop invariant 0 <= i <= len;
      @ loop assigns i, dst[0..len-1];
      @ loop variant len - i;
      */
    for (uint8_t i = 0; i < len; ++i) {
        dst[i] = src[i];
    }
    return;
}
/*@
  @ requires len > 0;
  @ requires \valid(dst+(0..len-1));
  @ assigns *(dst+(0..len-1));
  */
inline void FC_memset_ch(char *dst, char val, uint8_t len)
{

    /*@
      @ loop invariant 0 <= i <= len;
      @ loop assigns i, dst[0..len-1];
      @ loop variant len - i;
      */
    for (uint8_t i = 0; i < len; ++i) {
        dst[i] = val;
    }
    return;
}

#endif/*!__FRAMAC__*/
#endif/*!USBMSC_FRAMAC_PRIVATE_H_*/
