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
#include "libc/malloc.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "api/scsi.h"
#include "libc/string.h"
#include "usb_bbb.h"
#include "autoconf.h"
#include "libc/syscall.h"
#include "libc/arpa/inet.h"
#include "libusbctrl.h"
#include "libc/sync.h"

#include "usb_control_mass_storage.h"

#include "scsi.h"

#include "scsi_cmd.h"
#include "scsi_resp.h"
#include "scsi_log.h"
#include "scsi_automaton.h"

#include "libc/sanhandlers.h"


/*
 * The SCSI stack context. This is a global variable, which means
 * that the SCSI stack is not reentrant (not for scsi_context write access).
 * As most micro-controlers are not multicore based, this should not be
 * a problem.
 */


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
} scsi_context_t;


scsi_context_t scsi_ctx = {
    .direction = SCSI_DIRECTION_IDLE,
    .line_state = SCSI_TRANSMIT_LINE_READY,
    .size_to_process = 0,
    .addr = 0,
    .error = 0,
    .queue_empty = true,
    .global_buf = NULL,
    .global_buf_len = 0,
    .block_size = 0,
    .storage_size = 0,
};

static
#ifndef __FRAMAC__
volatile
#endif
cdb_t queued_cdb = { 0 };

static void scsi_error(scsi_sense_key_t sensekey, uint8_t asc, uint8_t ascq)
{
    log_printf("%s: %s: status=%d\n", __func__, __func__, sensekey);
    log_printf("%s: state -> Error\n", __func__);
    scsi_ctx.error = (sensekey << 16 | asc << 8 | ascq);
    /* returning status */
    usb_bbb_send_csw(CSW_STATUS_FAILED, 0);
    scsi_set_state(SCSI_IDLE);
}

/*********************************************************************
 * Mutexes, protection against race conditions...
 ********************************************************************/

/*
 * \brief entering a critical section
 *
 * During this critical section, any ISR is postponed to avoid any
 * race condition on variables shared in write-access between ISR and
 * main thread. See sys_lock() syscall API documentation.
 *
 * Critical sections must be as short as possible to avoid border
 * effects such as latency increase and ISR queue overloading.
 */
static inline mbed_error_t enter_critical_section(void)
{
    uint8_t ret;

    ret = sys_lock(LOCK_ENTER); /* Enter in critical section */
    if (ret != SYS_E_DONE) {
        log_printf("%s: Error: failed entering critical section!\n", __func__);
        return MBED_ERROR_BUSY;
    }
    return MBED_ERROR_NONE;
}

/*
 * \brief leaving a critical section
 *
 * Reallow the execution of the previously postponed task ISR.
 */
static inline void leave_critical_section(void)
{
    sys_lock(LOCK_EXIT);        /* Exit from critical section, should not
                                   fail */
    return;
}

/********* About debugging and pretty printing **************/

#if SCSI_DEBUG
static void scsi_debug_dump_cmd(cdb_t * current_cdb, uint8_t scsi_cmd)
{
    if (!current_cdb) {
        return;
    }
    if (SCSI_DEBUG < 2) {
        return;
    }
    switch (scsi_cmd) {
        case SCSI_CMD_MODE_SENSE_10:
            {
                log_printf("mode_sense_10:\n");
                log_printf("\treserved1          : %x\n",
                       current_cdb->payload.cdb10_mode_sense.LLBAA);
                log_printf("\tLLBAA              : %x\n",
                       current_cdb->payload.cdb10_mode_sense.LLBAA);
                log_printf("\tDBD                : %x\n",
                       current_cdb->payload.cdb10_mode_sense.DBD);
                log_printf("\treserved2          : %x\n",
                       current_cdb->payload.cdb10_mode_sense.reserved2);
                log_printf("\tPC                 : %x\n",
                       current_cdb->payload.cdb10_mode_sense.PC);
                log_printf("\tpage_code          : %x\n",
                       current_cdb->payload.cdb10_mode_sense.page_code);
                log_printf("\tsub_page_code      : %x\n",
                       current_cdb->payload.cdb10_mode_sense.sub_page_code);
                log_printf("\treserved3          : %x\n",
                       current_cdb->payload.cdb10_mode_sense.reserved3);
                log_printf("\tallocation_length  : %x\n",
                       current_cdb->payload.cdb10_mode_sense.allocation_length);
                log_printf("\tcontrol            : %x\n",
                       current_cdb->payload.cdb10_mode_sense.control);
                break;
            }
        case SCSI_CMD_MODE_SENSE_6:
            {
                log_printf("mode_sense_6:\n");
                log_printf("\tLUN                : %x\n",
                       current_cdb->payload.cdb6_mode_sense.LUN);
                log_printf("\treserved4          : %x\n",
                       current_cdb->payload.cdb6_mode_sense.reserved4);
                log_printf("\tDBD                : %x\n",
                       current_cdb->payload.cdb6_mode_sense.DBD);
                log_printf("\treserved3          : %x\n",
                       current_cdb->payload.cdb6_mode_sense.reserved3);
                log_printf("\tPC                 : %x\n",
                       current_cdb->payload.cdb6_mode_sense.PC);
                log_printf("\tpage_code          : %x\n",
                       current_cdb->payload.cdb6_mode_sense.page_code);
                log_printf("\treserved2          : %x\n",
                       current_cdb->payload.cdb6_mode_sense.reserved2);
                log_printf("\tallocation_length  : %x\n",
                       current_cdb->payload.cdb6_mode_sense.allocation_length);
                log_printf("\tvendor_specific    : %x\n",
                       current_cdb->payload.cdb6_mode_sense.vendor_specific);
                log_printf("\treserved1          : %x\n",
                       current_cdb->payload.cdb6_mode_sense.reserved1);
                log_printf("\tflag               : %x\n",
                       current_cdb->payload.cdb6_mode_sense.flag);
                log_printf("\tlink               : %x\n",
                       current_cdb->payload.cdb6_mode_sense.link);
                break;

            }
        case SCSI_CMD_INQUIRY:
            {
                log_printf("current_cdbuiry:\n");
                log_printf("CMDDT:         %x\n",
                       current_cdb->payload.cdb6_inquiry.CMDDT);
                log_printf("EVPD:          %x\n",
                       current_cdb->payload.cdb6_inquiry.EVPD);
                log_printf("page_code:     %x\n",
                       current_cdb->payload.cdb6_inquiry.page_code);
                log_printf("allocation_len:%x\n",
                       ntohs(current_cdb->payload.cdb6_inquiry.
                             allocation_length));
                log_printf("control  :     %x\n",
                       current_cdb->payload.cdb6_inquiry.control);
                break;
            }
        default:
            break;
    }
}
#endif

/******** End of debugging and pretty printing **************/


/********* About various utility functions     **************/

/*
 * Is the current context compatible with data reception ?
 */
static inline bool scsi_is_ready_for_data_receive(void)
{
    return ((scsi_ctx.direction == SCSI_DIRECTION_RECV
             || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY);
}

/*
 * Is the current context compatible with data transmission ?
 */
static inline bool scsi_is_ready_for_data_send(void)
{
    return ((scsi_ctx.direction == SCSI_DIRECTION_SEND
             || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY);
}


/*
 * Request data of given size from BULK stack.
 * This function is sending an asynchronous read request. The
 * read terminaison is acknowledge by a trigger on scsi_data_available()
 */
void scsi_get_data(void *buffer, uint32_t size)
{
#if SCSI_DEBUG > 1
    log_printf("%s: size: %d \n", __func__, size);
#endif
    while (!scsi_is_ready_for_data_receive()) {
        request_data_membarrier();
        continue;
    }

    set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_RECV);

    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_BUSY);
    scsi_ctx.addr = 0;
    request_data_membarrier();

    usb_bbb_recv(buffer, size);
}

/*
 * Request to send data of given size into the BULK stack.
 * This function is sending an asynchronous write request. The
 * transmission terminaison is acknowledge by a trigger on scsi_data_sent()
 */
void scsi_send_data(void *data, uint32_t size)
{
#if SCSI_DEBUG > 1
    log_printf("%s: size: %d \n", __func__, size);
#endif

    set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_SEND);
    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_BUSY);
    scsi_ctx.addr = 0;

    usb_bbb_send(data, size);        /* FIXME HARCODED ENDPOINT */
}

/*
 * Trigger on input data available
 */
static void scsi_data_available(uint32_t size)
{
#if SCSI_DEBUG > 1
    /* this function is triggered, printing trigger events is done only
     * on debug level 2 */
    aprintf("%s: %d\n", __func__, size);
#endif

    if (size >= scsi_ctx.size_to_process) {
        set_u32_with_membarrier(&scsi_ctx.size_to_process, 0);
    } else {
        set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.size_to_process - size);
    }
    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_READY);

    if (scsi_ctx.size_to_process == 0) {
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_IDLE);
        scsi_set_state(SCSI_IDLE);
    }
}


/*
 * Trigger on data sent by IP
 */
static void scsi_data_sent(void)
{
#if SCSI_DEBUG > 1
    /* this function is triggered, printing trigger events is done only
     * on debug level 2 */
    log_printf("%s\n", __func__);
#endif

    if (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.size_to_process - scsi_ctx.global_buf_len);
    } else {
        set_u32_with_membarrier(&scsi_ctx.size_to_process, 0);
    }
    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_READY);

    if (scsi_ctx.size_to_process == 0) {
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_IDLE);
        scsi_set_state(SCSI_IDLE);
    }
}


static void scsi_forge_mode_sense_response(u_mode_parameter * response,
                                           uint8_t mode)
{
    if (mode == SCSI_CMD_MODE_SENSE_6) {
        memset(response, 0x0, sizeof(mode_parameter6_data_t));
        /* We only send back the mode parameter header with no data */
        response->mode6.header.mode_data_length = 3;    /* The number of bytes that follow. */
        response->mode6.header.medium_type = 0; /* The media type SBC. */
        response->mode6.header.block_descriptor_length = 0;     /* A block descriptor length of zero indicates that no block descriptors */
        /* setting shortlba */
#if 0
        /* FIXME: Caching is buggy right now... */
        /* setting caching mode */
        response->mode6.caching.SPF = 0;
        response->mode6.caching.page_code = 0x08;
        response->mode6.caching.page_length = 0x12;
        response->mode6.caching.WCE = 0x1;
        response->mode6.caching.RCD = 0x1;
        response->mode6.caching.FSW = 0x1;
        response->mode6.caching.DRA = 0x1;
        response->mode6.caching.NV_DIS = 0x1;
#endif
    } else if (mode == SCSI_CMD_MODE_SENSE_10) {
        memset(response, 0x0, sizeof(mode_parameter10_data_t));
        /* We only send back the mode parameter header with no data */
        response->mode10.header.mode_data_length = 3;   /* The number of bytes that follow. */
        response->mode10.header.medium_type = 0;        /* The media type SBC. */
        response->mode10.header.block_descriptor_length = 0;    /* A block descriptor length of zero indicates that no block descriptors */
        response->mode10.header.longLBA = 0;
        /* are included in the mode parameter list. */
#if 0
        /* FIXME: Caching is buggy right now... */
        /* setting caching mode */
        response->mode10.caching.SPF = 0;
        response->mode10.caching.page_code = 0x08;
        response->mode10.caching.page_length = 0x12;
        response->mode10.caching.WCE = 0x1;
        response->mode10.caching.RCD = 0x1;
        response->mode10.caching.FSW = 0x1;
        response->mode10.caching.DRA = 0x1;
        response->mode10.caching.NV_DIS = 0x1;
#endif
    }
}


/************** End of utility functions **********************/


/*
 * SCSI automaton implementation.
 *
 * The SCSI automaton is based on two main entry points:
 * - scsi_parse_cdb, triggered by USB ISR when a SCSI command is received
 * - scsi_exec_automaton, which effectively execute the SCSI command, in
 *   main thread mode
 *
 * scsi_parse_cdb enqueue received command in the command queue. This functions
 * is as small as possible to reduce the ISR execution cost.
 * scsi_exec_automaton check for the command queue and dequeue commands to
 * execute them.
 *
 * All scsi_cmd_* procedures execute a given SCSI command. These procedures
 * are executed through scsi_exec_automaton.
 */

#ifndef __FRAMAC__
extern volatile bool reset_requested;
#else
extern bool reset_requested;
#endif


/*
 * Enqueue any received SCSI command
 * this function is executed in a handler context when a command comes from USB.
 */

/*@ requires cdb_len <= sizeof(cdb_t); */
static void scsi_parse_cdb(uint8_t cdb[], uint8_t cdb_len)
{
        if(reset_requested == true){
                while(reset_requested == true){
#ifdef __FRAMAC__
                    /* simulating concurent trigger when using framaC, to avoid endless loops */
                    reset_requested = false;
#endif
                    request_data_membarrier();
                    continue;
                }
                return;
        }
    /* Only up to 16 bytes commands are supported: bigger commands are truncated,
     * See cdb_t definition in scsi_cmd.h */
    memcpy((void *) &queued_cdb, (void *) cdb, cdb_len);
    set_bool_with_membarrier(&scsi_ctx.queue_empty, false);
    return;
}


/*
 * Commands implementation.
 *
 * All commands implementation check the SCSI state automaton to validate that
 * the transition is authorized, and then execute the command.
 */

/* SCSI_CMD_INQUIRY */
static void scsi_cmd_inquiry(scsi_state_t  current_state, cdb_t * cdb)
{
    inquiry_data_t response;
    cdb6_inquiry_t *inq;
    uint8_t next_state;

    log_printf("%s:\n", __func__);
    /* Sanity check */
    if (cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */

    if (!scsi_is_valid_transition(current_state, cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, cdb->operation);
    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    inq = &(cdb->payload.cdb6_inquiry);


#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(cdb, SCSI_CMD_INQUIRY);
#endif

    /* sanitize received cmd in conformity with SCSI standard */
    if (inq->EVPD == 0 && ntohs(inq->allocation_length) < 5) {
        /* invalid: additional fields parameter can't be send */
        goto invalid_cmd;
    }

    if (inq->EVPD == 1 && ntohs(inq->allocation_length) < 4) {
        /* invalid: additional fields parameter can't be send */
        goto invalid_cmd;
    }

    /* Most of support bits are set to 0
     * version is 0 because the device does not claim conformance to any
     * standard
     */
    memset((void *) &response, 0, sizeof(response));

    response.periph_device_type = 0x0;  /* direct access block device */
    response.RMB = 1;           /* Removable media */

    response.data_format = 2;   /* < 2 obsoletes, > 2 reserved */
    response.additional_len = sizeof(response) - 5;     /* (36 - 5) bytes after this one remain */
    response.additional_len = sizeof(response) - 5;     /* (36 - 5) bytes after this one remain */

    /* empty char must be set with spaces */
    memset(response.vendor_info, 0x20, sizeof(response.vendor_info));
    memcpy(response.vendor_info, CONFIG_USB_DEV_MANUFACTURER,
           strlen(CONFIG_USB_DEV_MANUFACTURER));
    /* empty char must be set with spaces */
    memset(response.product_identification, 0x20,
           sizeof(response.product_identification));
    memcpy(response.product_identification, CONFIG_USB_DEV_PRODNAME,
           strlen(CONFIG_USB_DEV_PRODNAME));

    memcpy(response.product_revision, CONFIG_USB_DEV_REVISION,
           strlen(CONFIG_USB_DEV_REVISION));

    log_printf("%s: %s\n", __func__, response.product_revision);


    if (inq->allocation_length > 0) {
        usb_bbb_send((uint8_t *) & response,
                     (ntohs(inq->allocation_length) <
                      sizeof(response)) ? ntohs(inq->
                                                allocation_length) :
                     sizeof(response));
    } else {
        log_printf("allocation length is 0\n");
    }
    return;

 invalid_cmd:
    log_printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


static void scsi_cmd_prevent_allow_medium_removal(scsi_state_t current_state,
                                                  cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);
    log_printf("%s: Prevent allow medium removal: %x\n", __func__,
           current_cdb->payload.cdb10_prevent_allow_removal.prevent);
    /* FIXME Add callback ? */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);

    return;
    /* effective transition execution (if needed) */

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


static void scsi_cmd_read_format_capacities(scsi_state_t current_state,
                                            cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    cdb12_read_format_capacities_t *rfc =
        &(current_cdb->payload.cdb12_read_format_capacities);

    capacity_list_t response = {
        .list_header.reserved_1            = 0,
        .list_header.reserved_2            = 0,
        .list_header.capacity_list_length  = 8,
        .cur_max_capacity.number_of_blocks = htonl(scsi_ctx.storage_size - 1),
        .cur_max_capacity.reserved         = 0,
        .cur_max_capacity.descriptor_code  = FORMATTED_MEDIA,
        .cur_max_capacity.block_length     = htonl(scsi_ctx.block_size),
        .num_format_descriptors            = 1,
        .formattable_descriptor.number_of_blocks =
		htonl(scsi_ctx.storage_size - 1),
        .formattable_descriptor.reserved  = 0,
        .formattable_descriptor.block_length = htonl(scsi_ctx.block_size)
    };

    /* we return only the current/max capacity descriptor, no formatable capacity descriptor, making the
     * response size the following: */
    uint32_t size =
        sizeof(capacity_list_header_t) +
        sizeof(curr_max_capacity_descriptor_t) + 1 +
        sizeof(formattable_capacity_descriptor_t);

    if (ntohs(rfc->allocation_length_msb) > 0) {
        usb_bbb_send((uint8_t *) & response,
                     (ntohs(rfc->allocation_length_msb) <
                      size) ? rfc->allocation_length_msb : size);
    } else {
        log_printf("allocation length is 0\n");
        usb_bbb_send((uint8_t *) & response, size);
    }
    return;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;

}

/*
 * SCSI_CMD_READ_6
 * INFO: this command is deprecated but is implemented for retrocompatibility
 * with older Operating Systems
 */
static void scsi_cmd_read_data6(scsi_state_t current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;
    uint8_t next_state;
    mbed_error_t error;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* entering READ state... */
    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t) current_cdb->payload.cdb6.logical_block)
        + (current_cdb->payload.cdb6.logical_block & 0x1f0000);

    rw_size = current_cdb->payload.cdb6.transfer_blocks;
    rw_addr = (uint64_t) scsi_ctx.block_size * (uint64_t) rw_lba;
    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.block_size * rw_size);

    total_num_sectors = scsi_ctx.size_to_process / scsi_ctx.block_size;
#if SCSI_DEBUG > 1
    log_printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__,
           scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif


    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_read(rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        /* send data we have just read */
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* increment read pointer */
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* active wait for data to be sent */
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {
#if SCSI_DEBUG > 1
        log_printf("%s: sending data residue to host.\n", __func__);
#endif
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_read((uint32_t) rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* active wait for data to be sent */
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
    }

 end:
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_READ_10 */
static void scsi_cmd_read_data10(scsi_state_t current_state,
                                 cdb_t * current_cdb)
{
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;
    uint8_t next_state;

    mbed_error_t error;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("current cdb is null\n");
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        log_printf("not valid transition from state %d\n", current_state);
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        log_printf("read capcity not yet set\n");
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* entering READ state... */
    scsi_set_state(next_state);

    rw_lba = ntohl(current_cdb->payload.cdb10.logical_block);
    rw_size = ntohs(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr = (uint64_t) scsi_ctx.block_size * (uint64_t) rw_lba;
    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.block_size * rw_size);

    total_num_sectors = scsi_ctx.size_to_process / scsi_ctx.block_size;
#if SCSI_DEBUG > 1
    log_printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__,
           scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif


    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_read(rw_lba, num_sectors);
        /* send data we have just read */
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* increment read pointer */
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* active wait for data to be sent */
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {
#if SCSI_DEBUG > 1
        log_printf("%s: sending data residue to host.\n", __func__);
#endif
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_read((uint32_t) rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* active wait for data to be sent */
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
    }
 end:
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_READ_CAPACITY_10 */
static void scsi_cmd_read_capacity10(scsi_state_t current_state,
                                     cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity10_parameter_data_t response;
    uint8_t ret;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);


    /* entering target state */
    scsi_set_state(next_state);

    /* let's get capacity from upper layer */
    ret =
        scsi_storage_backend_capacity(&(scsi_ctx.storage_size),
                                      &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (10) */

    response.ret_lba = htonl(scsi_ctx.storage_size - 1);
    response.ret_block_length = htonl(scsi_ctx.block_size);

    usb_bbb_send((uint8_t *) & response,
                 sizeof(read_capacity10_parameter_data_t));
    return;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_READ_CAPACITY_16 */
static void scsi_cmd_read_capacity16(scsi_state_t current_state,
                                     cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity16_parameter_data_t response;
    cdb16_read_capacity_16_t *rc16;
    uint8_t ret;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* entering target state */
    scsi_set_state(next_state);


    /* let's get capacity from upper layer */
    ret =
        scsi_storage_backend_capacity(&(scsi_ctx.storage_size),
                                      &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* get back cdb content from union */
    rc16 = &(current_cdb->payload.cdb16_read_capacity);

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (16) */

    /* creating response... */
    memset((void *) &response, 0x0, sizeof(read_capacity16_parameter_data_t));
    response.ret_lba = (uint64_t) htonl(scsi_ctx.storage_size - 1);
    response.ret_block_length = htonl(scsi_ctx.block_size);
    response.prot_enable = 0;   /* no prot_enable, protection associated fields
                                   are disabled. */
    response.rc_basis = 0x01;   /* LBA is the LBA of the last logical block
                                   on the logical unit. See Seagate SCSI
                                   command ref., chap. 3.23.2 */

#if SCSI_DEBUG > 1
    log_printf("%s: response[0]: %d response[1]: %d\n", __func__, response.ret_lba,
           response.ret_block_length);
#endif

    /* the amount of bytes sent in the response depends on the allocation
     * length value set in the read_capacity16 cmd. If this value is null,
     * no response should be sent.
     * See Seagate SCSI command ref. chap. 3.23.2 */
    if (rc16->allocation_length > 0) {
        usb_bbb_send((uint8_t *) & response,
                     (rc16->allocation_length < sizeof(response)) ?
		         rc16->allocation_length : sizeof(response));
    }
    return;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_REPORT_LUNS */
static void scsi_cmd_report_luns(scsi_state_t current_state,
                                 cdb_t * current_cdb)
{
    uint8_t next_state;
    cdb12_report_luns_t *rl;
    bool    check_condition = false;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);

    scsi_set_state(next_state);

    rl = &(current_cdb->payload.cdb12_report_luns);

    if (ntohs(rl->allocation_length) < 16) {
        /* invalid: requested to be at least 16 by standard */
        goto invalid_cmd;
    }
    if (ntohs(rl->allocation_length) < 24) {
        /* enable to send first lun informations */
        check_condition = true;
    }


    /* TODO We only support 1 LUN */
    report_luns_data_t response = {
        .lun_list_length = 1,
        .reserved = 0,
    };
    response.luns[0] = 0;

    /* sending response, up to required bytes */
    usb_bbb_send((uint8_t *) & response,
                 (ntohs(rl->allocation_length) <
                  sizeof(response)) ? ntohs(rl->
                                            allocation_length) :
                 sizeof(response));

    /* if the host didn't reserve enough space to respond, inform it that
     * some informations are missing */
    if (check_condition) {
        usb_bbb_send_csw(SCSI_STATUS_CHECK_CONDITION, 0);
    }
    return;

    /* XXX
     * If the logical unit inventory changes for any reason
     * (e.g., completion of initialization, removal of a logical unit, or creation of a logical unit),
     * then the device server shall establish a unit attention condition (see SAM-3) for the
     * initiator port associated with every I_T nexus, with the additional sense code set
     * to REPORTED LUNS DATA HAS CHANGED.
     */


 invalid_cmd:
    log_printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_REQUEST_SENSE */
static void scsi_cmd_request_sense(scsi_state_t current_state,
                                   cdb_t * current_cdb)
{
    uint8_t next_state;
    request_sense_parameter_data_t data;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    log_printf("%s: desc: %x, allocation_length: %x\n",
           current_cdb->payload.cdb10_request_sense.desc,
           current_cdb->payload.cdb10_request_sense.allocation_length);
#endif

    /* TODO If desc is set to 1 and descriptor format sense data is supported */

    /* descriptor format sense data shall be returned. */

    memset((void *) &data, 0, sizeof(data));
    data.error_code = 0x70;
    data.sense_key = scsi_error_get_sense_key(scsi_ctx.error);
    data.additional_sense_length = 0x0a;
    data.asc = scsi_error_get_asc(scsi_ctx.error);
    data.ascq = scsi_error_get_ascq(scsi_ctx.error);
    /* now that data has been sent successfully, scsi error is cleared */
    scsi_ctx.error = 0;

    usb_bbb_send((uint8_t *) & data, sizeof(data));
    return;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}



/* SCSI_CMD_MODE_SENSE(10) */
static void scsi_cmd_mode_sense10(scsi_state_t current_state,
                                  cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    /* Sending Mode Sense 10 answer */
    mode_parameter10_data_t response;

    scsi_forge_mode_sense_response((u_mode_parameter *) & response,
                                   SCSI_CMD_MODE_SENSE_10);
    /* Sending Mode Sense 10 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *) & response, sizeof(mode_parameter10_data_t));

    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_MODE_SENSE(6) */
static void scsi_cmd_mode_sense6(scsi_state_t current_state,
                                 cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    mode_parameter6_data_t response;

    scsi_forge_mode_sense_response((u_mode_parameter *) & response,
                                   SCSI_CMD_MODE_SENSE_6);
    /* Sending Mode Sense 10 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *) & response, sizeof(mode_parameter6_data_t));
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_MODE_SELECT(6) */
static void scsi_cmd_mode_select6(scsi_state_t current_state,
                                  cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_MODE_SELECT(10) */
static void scsi_cmd_mode_select10(scsi_state_t current_state,
                                   cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_TEST_UNIT_READY */
static void scsi_cmd_test_unit_ready(scsi_state_t current_state,
                                     cdb_t * current_cdb)
{
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check */
    if (current_cdb == NULL) {
        log_printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/*
 * SCSI_CMD_WRITE(6)
 * This command is declared as obsolete by the T10 consorsium.
 * It is implemented here for retrocompatibility with old Operating System
 */
static void scsi_write_data6(scsi_state_t current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;
    uint8_t next_state;

    log_printf("%s:\n", __func__);

    if (current_cdb == NULL) {
        return;
    }

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);

    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }


    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t) current_cdb->payload.cdb6.logical_block)
        + (current_cdb->payload.cdb6.logical_block & 0x1f0000);
    rw_size = current_cdb->payload.cdb6.transfer_blocks;
    rw_addr = (uint64_t) scsi_ctx.block_size * (uint64_t) rw_lba;

    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.block_size * rw_size);


#if SCSI_DEBUG > 1
    uint32_t total_num_sectors = rw_size;

    log_printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__,
           scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif

    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
	/* Wait until we have indeed received data from the USB lower layers */
	while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
#ifdef __FRAMAC__
        /* emulating asynchronous trigger */
        scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;
#endif
        request_data_membarrier();
		continue;
	}
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }

    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
	/* Wait until we have indeed received data from the USB lower layers */
	while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
#ifdef __FRAMAC__
        /* emulating asynchronous trigger */
        scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;
#endif
        request_data_membarrier();
		continue;
	}
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
    }
 end:
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}



/* SCSI_CMD_WRITE(10) */
static void scsi_write_data10(scsi_state_t current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;
    uint8_t next_state;

    log_printf("%s:\n", __func__);

    if (current_cdb == NULL) {
        return;
    }

    /* Sanity check */
    if (current_cdb == NULL) {
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }


    rw_lba = ntohl(current_cdb->payload.cdb10.logical_block);
    rw_size = ntohs(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr = (uint64_t) scsi_ctx.block_size * (uint64_t) rw_lba;

    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    set_u32_with_membarrier(&scsi_ctx.size_to_process, scsi_ctx.block_size * rw_size);


#if SCSI_DEBUG > 1
    uint32_t total_num_sectors = rw_size;

    log_printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__,
           scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif

    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
	/* Wait until we have indeed received data from the USB lower layers */
	while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
#ifdef __FRAMAC__
        /* emulating asynchronous trigger */
        scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;
#endif
        request_data_membarrier();
		continue;
	}
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }

    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        /* Wait until we have indeed received data from the USB lower layers */
        while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
#ifdef __FRAMAC__
            /* emulating asynchronous trigger */
            scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;
#endif
            request_data_membarrier();
            continue;
        }
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
    }
 end:
    return;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

mbed_error_t scsi_initialize_automaton(void)
{
    /* read first command */
    read_next_cmd();
    return MBED_ERROR_NONE;
}

/*
 * SCSI Automaton execution
 */
void scsi_exec_automaton(void)
{
    /* local cdb copy */
    cdb_t   local_cdb;

    if (scsi_ctx.queue_empty == true) {
        request_data_membarrier();
        return;
    }

    /* critical section part. This part of the code is handling
     * the command queue to get back the queued cdb block from it.
     */
    if (enter_critical_section() != MBED_ERROR_NONE) {
        /* unable to enter critical section by now... leaving current turn */
        log_printf("Unable to enter critical section!\n");
        goto nothing_to_do;
    }
    memcpy((void *) &local_cdb, (void *) &queued_cdb, sizeof(cdb_t));
    /* we handle a signe command at a time, which is standard for the
     * SCSI automaton, as SCSI is syncrhonous */
    set_bool_with_membarrier(&scsi_ctx.queue_empty, true);

    leave_critical_section();
    /* end of the critical section part. From now one, ISR can
     * be executed again
     */

    scsi_state_t current_state = scsi_get_state();

    switch (local_cdb.operation) {
        case SCSI_CMD_INQUIRY:
            scsi_cmd_inquiry(current_state, &local_cdb);
            break;

        case SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL:
            scsi_cmd_prevent_allow_medium_removal(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_6:
            scsi_cmd_read_data6(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_10:
            scsi_cmd_read_data10(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_CAPACITY_10:
            scsi_cmd_read_capacity10(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_CAPACITY_16:
            scsi_cmd_read_capacity16(current_state, &local_cdb);
            break;

        case SCSI_CMD_REPORT_LUNS:
            scsi_cmd_report_luns(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_FORMAT_CAPACITIES:
            scsi_cmd_read_format_capacities(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SELECT_10:
            scsi_cmd_mode_select10(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SELECT_6:
            scsi_cmd_mode_select6(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SENSE_10:
            scsi_cmd_mode_sense10(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SENSE_6:
            scsi_cmd_mode_sense6(current_state, &local_cdb);
            break;


        case SCSI_CMD_REQUEST_SENSE:
            scsi_cmd_request_sense(current_state, &local_cdb);
            break;
#if 0
        case SCSI_CMD_SEND_DIAGNOSTIC:
            scsi_cmd_send_diagnostic(current_state, &local_cdb);
            break;
#endif
        case SCSI_CMD_TEST_UNIT_READY:
            scsi_cmd_test_unit_ready(current_state, &local_cdb);
            break;

        case SCSI_CMD_WRITE_6:
            scsi_write_data6(current_state, &local_cdb);
            break;

        case SCSI_CMD_WRITE_10:
            scsi_write_data10(current_state, &local_cdb);
            break;

        default:
            log_printf("%s: Unsupported command: %x  \n", __func__,
                   local_cdb.operation);
            scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                       ASCQ_NO_ADDITIONAL_SENSE);
            break;
    };
    return;

 nothing_to_do:
    return;
}


/*
 * Resetting SCSI context. Should be executed as a trigger of BULK level
 * USB reset order
 */
static void scsi_reset_context(void)
{
    log_printf("[reset] clearing USB context\n");
    /* resetting the context in a known, empty, idle state */
    set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_IDLE);
    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_READY);
    set_u32_with_membarrier(&scsi_ctx.size_to_process, 0);
    scsi_ctx.addr = 0;
    scsi_ctx.error = 0;
    set_bool_with_membarrier(&scsi_ctx.queue_empty, true);
    scsi_ctx.block_size = 0;
    scsi_ctx.storage_size = 0;
    scsi_set_state(SCSI_IDLE);
    request_data_membarrier();
}


/*
 * At earlu init time, no usbctrl interaction, only local SCSI & BBB configuration
 */
mbed_error_t scsi_early_init(uint8_t * buf, uint16_t len)
{

    log_printf("%s\n", __func__);

    if (!buf) {
        goto init_error;
    }

    scsi_ctx.global_buf = buf;
    scsi_ctx.global_buf_len = len;

    /* Register our callbacks as valid ones */
#ifndef __FRAMAC__
    ADD_LOC_HANDLER(scsi_parse_cdb)
    ADD_LOC_HANDLER(scsi_data_available)
    ADD_LOC_HANDLER(scsi_data_sent)
#endif
    usb_bbb_declare(scsi_parse_cdb, scsi_data_available, scsi_data_sent);

    /* TODO: push down to usb_bbb lower layer ? */

    return MBED_ERROR_NONE;

 init_error:
    log_printf("%s: ERROR: Unable to initialize scsi stack : %x  \n", __func__,
           MBED_ERROR_INVPARAM);
    return MBED_ERROR_INVPARAM;
}

/*
 * Init
 */

/*
 * Here, this is the effective initialization of the device, we:
 * 1) configure the SCSI context and queue
 * 2)
 */
mbed_error_t scsi_init(uint32_t usbdci_handler)
{
    uint32_t i;

    log_printf("%s\n", __func__);

    /* in USB High speed mode, the USB device is mapped (and enabled) just now */
    /* declare interface to libusbctrl  */


    scsi_ctx.storage_size = 0;
    scsi_ctx.block_size = 4096; /* default */
    scsi_set_state(SCSI_IDLE);

    for (i = 0; i < scsi_ctx.global_buf_len; i++) {
        scsi_ctx.global_buf[i] = '\0';
    }

    /* Register our callbacks on the lower layer, declaring iface to
     * usbctrl */
    usb_bbb_configure(usbdci_handler);

    scsi_set_state(SCSI_IDLE);

    /* initialize control plane, adding the reset event trigger for SCSI level */

    return MBED_ERROR_NONE;
}

void scsi_reinit(void)
{
    usb_bbb_reconfigure();
    scsi_reset_context();
}
