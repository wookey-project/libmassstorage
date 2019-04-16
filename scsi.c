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
#include "libc/queue.h"
#include "usb.h"
#include "usb_bbb.h"
#include "autoconf.h"
#include "libc/syscall.h"
#include "libc/arpa/inet.h"
#include "wookey_ipc.h"

#include "usb_control_mass_storage.h"

#include "scsi_cmd.h"
#include "scsi_resp.h"
#include "scsi_log.h"
#include "scsi_automaton.h"

#define SCSI_DEBUG 0

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


typedef  struct {
    volatile transmission_direction_t direction;
    volatile transmition_line_state_t line_state;
    volatile uint32_t size_to_process;
    uint32_t addr;
    uint32_t error;
    queue_t *queue; /* used to avoid lock loop */
    volatile bool     queue_empty;
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
    .error= 0,
    .queue=NULL,
    .queue_empty = true,
    .global_buf = NULL,
    .global_buf_len = 0,
    .block_size = 0,
    .storage_size = 0,
};



static volatile cdb_t queued_cdb = { 0 };

static void scsi_error(scsi_sense_key_t sensekey, uint8_t asc, uint8_t ascq){
#if SCSI_DEBUG
    aprintf("%s: %s: status=%d\n", __func__, __func__, sensekey);
    aprintf("%s: state -> Error\n",__func__);
#endif
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
    ret = sys_lock (LOCK_ENTER); /* Enter in critical section */
    if(ret != SYS_E_DONE){
        printf("%s: Error: failed entering critical section!\n", __func__);
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
    sys_lock (LOCK_EXIT);  /* Exit from critical section, should not
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
            printf("mode_sense_10:\n");
            printf("\treserved1          : %x\n", current_cdb->payload.cdb10_mode_sense.LLBAA);
            printf("\tLLBAA              : %x\n", current_cdb->payload.cdb10_mode_sense.LLBAA);
            printf("\tDBD                : %x\n", current_cdb->payload.cdb10_mode_sense.DBD);
            printf("\treserved2          : %x\n", current_cdb->payload.cdb10_mode_sense.reserved2);
            printf("\tPC                 : %x\n", current_cdb->payload.cdb10_mode_sense.PC);
            printf("\tpage_code          : %x\n", current_cdb->payload.cdb10_mode_sense.page_code);
            printf("\tsub_page_code      : %x\n", current_cdb->payload.cdb10_mode_sense.sub_page_code);
            printf("\treserved3          : %x\n", current_cdb->payload.cdb10_mode_sense.reserved3);
            printf("\tallocation_length  : %x\n", current_cdb->payload.cdb10_mode_sense.allocation_length);
            printf("\tcontrol            : %x\n", current_cdb->payload.cdb10_mode_sense.control);
            break;
        }
        case SCSI_CMD_MODE_SENSE_6:
        {
            printf("mode_sense_6:\n");
            printf("\tLUN                : %x\n", current_cdb->payload.cdb6_mode_sense.LUN);
            printf("\treserved4          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved4);
            printf("\tDBD                : %x\n", current_cdb->payload.cdb6_mode_sense.DBD);
            printf("\treserved3          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved3);
            printf("\tPC                 : %x\n", current_cdb->payload.cdb6_mode_sense.PC);
            printf("\tpage_code          : %x\n", current_cdb->payload.cdb6_mode_sense.page_code);
            printf("\treserved2          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved2);
            printf("\tallocation_length  : %x\n", current_cdb->payload.cdb6_mode_sense.allocation_length);
            printf("\tvendor_specific    : %x\n", current_cdb->payload.cdb6_mode_sense.vendor_specific);
            printf("\treserved1          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved1);
            printf("\tflag               : %x\n", current_cdb->payload.cdb6_mode_sense.flag);
            printf("\tlink               : %x\n", current_cdb->payload.cdb6_mode_sense.link);
            break;

        }
        case SCSI_CMD_INQUIRY:
        {
            printf("current_cdbuiry:\n");
            printf("CMDDT:         %x\n", current_cdb->payload.cdb6_inquiry.CMDDT);
            printf("EVPD:          %x\n", current_cdb->payload.cdb6_inquiry.EVPD);
            printf("page_code:     %x\n", current_cdb->payload.cdb6_inquiry.page_code);
            printf("allocation_len:%x\n", ntohs(current_cdb->payload.cdb6_inquiry.allocation_length));
            printf("control  :     %x\n", current_cdb->payload.cdb6_inquiry.control);
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
 * Release the current CDB structure
 */
static mbed_error_t scsi_release_cdb(cdb_t * current_cdb)
{
    /* no critical section here, as the exec_automaton
     * is not reentrant and is fully exec in main thread mode.
     * The current_cdb variable is a local only variable.
     */
    mbed_error_t ret = MBED_ERROR_NONE;
	if(current_cdb != NULL) {
		if(wfree((void**)&current_cdb)) {
            /* should not arrise */
            ret = MBED_ERROR_UNKNOWN;
		}
	}
	current_cdb = NULL;
    return ret;
}

/*
 * Is the current context compatible with data reception ?
 */
static inline bool scsi_is_ready_for_data_receive(void)
{
    return (   (   scsi_ctx.direction == SCSI_DIRECTION_RECV
                || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY );
}

/*
 * Is the current context compatible with data transmission ?
 */
static inline bool scsi_is_ready_for_data_send(void)
{
    return (   (   scsi_ctx.direction == SCSI_DIRECTION_SEND
                || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY );
}


/*
 * Request data of given size from BULK stack.
 * This function is sending an asynchronous read request. The
 * read terminaison is acknowledge by a trigger on scsi_data_available()
 */
void scsi_get_data(void *buffer, uint32_t size)
{
#if SCSI_DEBUG
	printf("%s: size: %d \n", __func__, size );
#endif
	while(!scsi_is_ready_for_data_receive()){
		continue;
	}

	scsi_ctx.direction = SCSI_DIRECTION_RECV;
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_BUSY;
    scsi_ctx.addr = 0;

	usb_bbb_read(buffer, size, 1);
}

/*
 * Request to send data of given size into the BULK stack.
 * This function is sending an asynchronous write request. The
 * transmission terminaison is acknowledge by a trigger on scsi_data_sent()
 */
void scsi_send_data(void *data, uint32_t size)
{
#if SCSI_DEBUG
	printf("%s: size: %d \n", __func__, size );
#endif

	scsi_ctx.direction = SCSI_DIRECTION_SEND;
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_BUSY;
    scsi_ctx.addr = 0;

	usb_bbb_send(data, size, 2); /* FIXME HARCODED ENDPOINT */
}

/*
 * Trigger on input data available
 */
static void scsi_data_available(uint32_t size)
{
#if SCSI_DEBUG
    aprintf("%s: %d\n", __func__, size);
#endif

    if (size >= scsi_ctx.size_to_process) {
        scsi_ctx.size_to_process = 0;
    } else {
        scsi_ctx.size_to_process -= size;
    }
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;

    if (scsi_ctx.size_to_process == 0){
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        scsi_ctx.direction = SCSI_DIRECTION_IDLE;
        scsi_set_state(SCSI_IDLE);
    }
}


/*
 * Trigger on data sent by IP
 */
static void scsi_data_sent(void)
{
#if SCSI_DEBUG
    aprintf("%s\n", __func__);
#endif

    if (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_ctx.size_to_process -= scsi_ctx.global_buf_len;
    } else {
        scsi_ctx.size_to_process = 0;
    }
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;

    if (scsi_ctx.size_to_process == 0) {
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        scsi_ctx.direction = SCSI_DIRECTION_IDLE;
        scsi_set_state(SCSI_IDLE);
    }
}


static void scsi_forge_mode_sense_response(u_mode_parameter *response, uint8_t mode)
{
    memset(response, 0x0, sizeof(u_mode_parameter));
    if (mode == SCSI_CMD_MODE_SENSE_6) {
        /* We only send back the mode parameter header with no data */
        response->mode6.header.mode_data_length = 3;        /* The number of bytes that follow. */
        response->mode6.header.medium_type = 0;             /* The media type SBC. */
        response->mode6.header.block_descriptor_length = 0; /* A block descriptor length of zero indicates that no block descriptors */
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
        /* We only send back the mode parameter header with no data */
        response->mode10.header.mode_data_length = 3;        /* The number of bytes that follow. */
        response->mode10.header.medium_type = 0;             /* The media type SBC. */
        response->mode10.header.block_descriptor_length = 0; /* A block descriptor length of zero indicates that no block descriptors */
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


/*
 * Enqueue any received SCSI command
 * this function is executed in a handler context when a command comes from USB.
 */
static void scsi_parse_cdb(uint8_t cdb[], uint8_t cdb_len __attribute__((unused)))
{
    /* Only up to 16 bytes commands are supported: bigger commands are truncated,
     * See cdb_t definition in scsi_cmd.h */
    memcpy((void*)&queued_cdb, (void*)cdb, sizeof(cdb_t));
    scsi_ctx.queue_empty = false;
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

#if SCSI_DEBUG
		printf("%s:\n", __func__ );
#endif
    /* Sanity check */
    if(cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, cdb->operation);

    if (!scsi_is_valid_transition(current_state, cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, cdb->operation);

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
	memset((void *)&response, 0, sizeof(response));

    response.periph_device_type = 0x0; /* direct access block device */
	response.RMB = 1;                           /* Removable media */

	response.data_format = 2;                   /* < 2 obsoletes, > 2 reserved */
	response.additional_len = sizeof(response) - 5; /* (36 - 5) bytes after this one remain */
    response.additional_len = sizeof(response) - 5; /* (36 - 5) bytes after this one remain */

    /* empty char must be set with spaces */
    memset(response.vendor_info, 0x20, sizeof(response.vendor_info));
    memcpy(response.vendor_info, CONFIG_USB_DEV_MANUFACTURER, sizeof(response.vendor_info));
    /* empty char must be set with spaces */
    memset(response.product_identification, 0x20, sizeof(response.product_identification));
    memcpy(response.product_identification, CONFIG_USB_DEV_PRODNAME, sizeof(response.product_identification));

    memcpy(response.product_revision, CONFIG_USB_DEV_REVISION, sizeof(response.product_revision));

#if SCSI_DEBUG
    printf("%s: %s\n",__func__, response.product_revision);
#endif


    if (inq->allocation_length > 0) {
        usb_bbb_send((uint8_t *)&response, (ntohs(inq->allocation_length) < sizeof(response)) ? ntohs(inq->allocation_length) : sizeof(response), 2);
    } else {
        printf("allocation length is 0\n");
    }
    return;

invalid_cmd:
    printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


static void scsi_cmd_prevent_allow_medium_removal(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);
#if SCSI_DEBUG
    printf("%s: Prevent allow medium removal: %x\n",__func__, current_cdb->payload.cdb10_prevent_allow_removal.prevent);
#endif
    /* FIXME Add callback ? */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;
    /* effective transition execution (if needed) */

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/*
 * SCSI_CMD_READ_6
 * INFO: this command is deprecated but is implemented for retrocompatibility
 * with older Operating Systems
 */
static void scsi_cmd_read_data6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;
    mbed_error_t error;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* entering READ state... */
    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t)current_cdb->payload.cdb6.logical_block)
        + (current_cdb->payload.cdb6.logical_block & 0x1f0000);

    rw_size = current_cdb->payload.cdb6.transfer_blocks;
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;
    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;

    total_num_sectors = scsi_ctx.size_to_process / scsi_ctx.block_size;
    #if SCSI_DEBUG
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
    #endif


    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_read(rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        /* send data we have just read */
		scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* increment read pointer */
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {
#if SCSI_DEBUG
        printf("%s: sending data residue to host.\n", __func__);
#endif
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_read((uint32_t)rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
#if SCSI_DEBUG
        #endif
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }

end:
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_READ_10 */
static void scsi_cmd_read_data10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* entering READ state... */
    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    rw_lba = ntohl(current_cdb->payload.cdb10.logical_block);
    rw_size = ntohs(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;
    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;

    total_num_sectors = scsi_ctx.size_to_process / scsi_ctx.block_size;
    #if SCSI_DEBUG
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
    #endif


    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_read(rw_lba, num_sectors);
        /* send data we have just read */
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
		scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* increment read pointer */
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {
#if SCSI_DEBUG
        printf("%s: sending data residue to host.\n", __func__);
#endif
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_read((uint32_t)rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
#if SCSI_DEBUG
        #endif
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }
end:
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_READ_CAPACITY_10 */
static void scsi_cmd_read_capacity10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity10_parameter_data_t response;
    uint8_t ret;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);


    /* let's get capacity from upper layer */
    ret = scsi_storage_backend_capacity(&(scsi_ctx.storage_size), &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (10) */

	response.ret_lba = htonl(scsi_ctx.storage_size-1);
	response.ret_block_length = htonl(scsi_ctx.block_size);

    usb_bbb_send((uint8_t *)&response, sizeof(read_capacity10_parameter_data_t), 2);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_READ_CAPACITY_16 */
static void scsi_cmd_read_capacity16(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity16_parameter_data_t response;
    cdb16_read_capacity_16_t *rc16;
    uint8_t ret;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);


    /* let's get capacity from upper layer */
    ret = scsi_storage_backend_capacity(&(scsi_ctx.storage_size), &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }

    /* get back cdb content from union */
    rc16 = &(current_cdb->payload.cdb16_read_capacity);

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (16) */

    /* creating response... */
    memset((void*)&response, 0x0, sizeof(read_capacity16_parameter_data_t));
	response.ret_lba = (uint64_t)htonl(scsi_ctx.storage_size-1);
	response.ret_block_length = htonl(scsi_ctx.block_size);
    response.prot_enable = 0; /* no prot_enable, protection associated fields
                                 are disabled. */
    response.rc_basis = 0x01; /* LBA is the LBA of the last logical block
                                 on the logical unit. See Seagate SCSI
                                 command ref., chap. 3.23.2 */

    #if SCSI_DEBUG
        printf("%s: response[0]: %d response[1]: %d\n", __func__, response.ret_lba, response.ret_block_length);
    #endif

    /* the amount of bytes sent in the response depends on the allocation
     * length value set in the read_capacity16 cmd. If this value is null,
     * no response should be sent.
     * See Seagate SCSI command ref. chap. 3.23.2 */
    if (rc16->allocation_length > 0) {
        usb_bbb_send((uint8_t *)&response, (rc16->allocation_length < sizeof(response)) ? rc16->allocation_length : sizeof(response), 2);
    }
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_REPORT_LUNS */
static void scsi_cmd_report_luns(scsi_state_t  current_state, cdb_t * current_cdb)
{
    cdb12_report_luns_t *rl;
    bool check_condition = false;
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (next_state != 0xff) {
        scsi_set_state(next_state);
    } else {
        goto invalid_transition;
    }

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
    usb_bbb_send((uint8_t *)&response, (ntohs(rl->allocation_length) < sizeof(response)) ? ntohs(rl->allocation_length) : sizeof(response), 2);

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
    printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_REQUEST_SENSE */
static void scsi_cmd_request_sense(scsi_state_t  current_state, cdb_t * current_cdb)
{
    request_sense_parameter_data_t data;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

#if SCSI_DEBUG
    printf( "%s: desc: %x, allocation_length: %x\n",
            current_cdb->payload.cdb10_request_sense.desc,
            current_cdb->payload.cdb10_request_sense.allocation_length);
#endif

    /* TODO If desc is set to 1 and descriptor format sense data is supported */

    /* descriptor format sense data shall be returned. */

	memset((void *)&data, 0, sizeof(data));
	data.error_code = 0x70;
	data.sense_key = scsi_error_get_sense_key(scsi_ctx.error);
	data.additional_sense_length = 0x0a;
	data.asc = scsi_error_get_asc(scsi_ctx.error);
	data.ascq = scsi_error_get_ascq(scsi_ctx.error);
    /* now that data has been sent successfully, scsi error is cleared */
    scsi_ctx.error = 0;

	usb_bbb_send((uint8_t *)&data, sizeof(data), 2);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}



/* SCSI_CMD_MODE_SENSE(10) */
static void scsi_cmd_mode_sense10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    /* Sending Mode Sense 10 answer */
    mode_parameter10_data_t response;
    scsi_forge_mode_sense_response((u_mode_parameter*)&response, SCSI_CMD_MODE_SENSE_10);
    /* Sending Mode Sense 10 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *)&response, sizeof(mode_parameter10_data_t), 2);

    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_MODE_SENSE(6) */
static void scsi_cmd_mode_sense6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    mode_parameter6_data_t response;
    scsi_forge_mode_sense_response((u_mode_parameter*)&response, SCSI_CMD_MODE_SENSE_6);
    /* Sending Mode Sense 10 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *)&response, sizeof(mode_parameter6_data_t), 2);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/* SCSI_CMD_MODE_SELECT(6) */
static void scsi_cmd_mode_select6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_MODE_SELECT(10) */
static void scsi_cmd_mode_select10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}


/* SCSI_CMD_TEST_UNIT_READY */
static void scsi_cmd_test_unit_ready(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/*
 * SCSI_CMD_WRITE(6)
 * This command is declared as obsolete by the T10 consorsium.
 * It is implemented here for retrocompatibility with old Operating System
 */
static void scsi_write_data6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;

#if SCSI_DEBUG
    printf("%s:\n",__func__);
#endif

	if(current_cdb == NULL){
		return;
	}

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (next_state != 0xff) {
        scsi_set_state(next_state);
    } else {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }


    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t)current_cdb->payload.cdb6.logical_block)
        + (current_cdb->payload.cdb6.logical_block & 0x1f0000);
    rw_size = current_cdb->payload.cdb6.transfer_blocks;
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;

    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;


#if SCSI_DEBUG
    uint32_t total_num_sectors = rw_size;
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif

    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        while(!scsi_is_ready_for_data_receive()){
            continue;
        }

    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        while(!scsi_is_ready_for_data_receive()){
            continue;
        }
    }
end:
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}



/* SCSI_CMD_WRITE(10) */
static void scsi_write_data10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;

#if SCSI_DEBUG
    printf("%s:\n",__func__);
#endif

	if(current_cdb == NULL){
		return;
	}

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (next_state != 0xff) {
        scsi_set_state(next_state);
    } else {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
        return;
    }


    rw_lba = ntohl(current_cdb->payload.cdb10.logical_block);
    rw_size = ntohs(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;

    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;


#if SCSI_DEBUG
    uint32_t total_num_sectors = rw_size;
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif

    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        while(!scsi_is_ready_for_data_receive()){
            continue;
        }

    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR, ASCQ_NO_ADDITIONAL_SENSE);
            goto end;
        }
        while(!scsi_is_ready_for_data_receive()){
            continue;
        }
    }
end:
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
    return;
}

/*
 * SCSI Automaton execution
 */
void scsi_exec_automaton(void)
{
    /* local cdb copy */
    cdb_t local_cdb;

    if (scsi_ctx.queue_empty == true) {
        return;
    }

    usb_ctrl_set_initphase_done();

    /* critical section part. This part of the code is handling
     * the command queue to get back the queued cdb block from it.
     */
    if (enter_critical_section() != MBED_ERROR_NONE) {
        /* unable to enter critical section by now... leaving current turn */
        printf("Unable to enter critical section!\n");
        goto nothing_to_do;
    }
    memcpy((void*)&local_cdb, (void*)&queued_cdb, sizeof(cdb_t));
    /* we handle a signe command at a time, which is standard for the
     * SCSI automaton, as SCSI is syncrhonous */
    scsi_ctx.queue_empty = true;

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
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE, ASCQ_NO_ADDITIONAL_SENSE);
#if SCSI_DEBUG
        printf("%s: Unsupported command: %x  \n", __func__, &local_cdb.operation);
#endif
	};

    return;

nothing_to_do:
    return;
}


typedef enum scsi_init_error {
    SCSI_INIT_DONE = 0x00,
    SCSI_INIT_CALLBACK_ERROR,
    SCSI_INIT_BUFFER_ERROR,
} scsi_init_error_t;

/*
 * Resetting SCSI context. Should be executed as a trigger of BULK level
 * USB reset order
 */
static void scsi_reset_context(void)
{
    aprintf("[reset] clearing USB context\n");
    /* resetting the context in a known, empty, idle state */
    scsi_ctx.direction = SCSI_DIRECTION_IDLE;
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;
    scsi_ctx.size_to_process = 0;
    scsi_ctx.addr = 0;
    scsi_ctx.error= 0;
    scsi_ctx.queue_empty = true;
    scsi_ctx.block_size = 0;
    scsi_ctx.storage_size = 0;
    scsi_set_state(SCSI_IDLE);
}


uint8_t scsi_early_init(uint8_t *buf, uint16_t len)
{

    scsi_init_error_t error = -1;
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    if ( !buf ) {
        error = SCSI_INIT_BUFFER_ERROR;
        goto init_error;
    }

    if ( len <= 0 ) {
        error = SCSI_INIT_BUFFER_ERROR;
        goto init_error;
    }

    scsi_ctx.global_buf = buf;
    scsi_ctx.global_buf_len = len;

	usb_bbb_early_init(scsi_parse_cdb, scsi_data_available, scsi_data_sent);
    return 0;

init_error:
#if SCSI_DEBUG
    printf("%s: ERROR: Unable to initialize scsi stack : %x  \n", __func__, error);
#endif
    return 1;
}

/*
 * Init
 */
#define MAX_SCSI_CMD_QUEUE_SIZE 10

mbed_error_t scsi_init(void)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* in USB High speed mode, the USB device is mapped (and enabled) just now */
    usb_driver_map();

	unsigned int i;

    scsi_ctx.storage_size = 0;
    scsi_ctx.block_size = 4096; /* default */
    scsi_set_state(SCSI_IDLE);

	if (queue_create(MAX_SCSI_CMD_QUEUE_SIZE, &scsi_ctx.queue) != MBED_ERROR_NONE) {
        return MBED_ERROR_NOMEM;
    }

	for(i = 0; i < scsi_ctx.global_buf_len; i++){
		scsi_ctx.global_buf[i] = i;
	}

	/* Register our callbacks on the lower layer */
	usb_bbb_init();

    scsi_set_state(SCSI_IDLE);

    /* initialize control plane, adding the reset event trigger for SCSI level */
    mass_storage_init(scsi_reset_context, scsi_reset_device);
    return MBED_ERROR_NONE;
}


