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
#include "autoconf.h"
#include "libc/malloc.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/stdint.h"
#include "libc/arpa/inet.h"
#include "libc/syscall.h"
#include "libc/sync.h"

#include "libusbctrl.h"
#include "api/scsi.h"
#include "usb_bbb.h"

#include "usb_control_mass_storage.h"

#include "scsi_dbg.h"

#include "scsi.h"
#include "scsi_cmd.h"
#include "scsi_resp.h"
#include "scsi_log.h"
#include "scsi_automaton.h"

#include "libc/sanhandlers.h"

#ifdef __FRAMAC__
/* requested to access entropy sources to emulate backend errors */
# include "framac/entrypoint.h"
#endif


/*
 * The SCSI stack context. This is a global variable, which means
 * that the SCSI stack is not reentrant (not for scsi_context write access).
 * As most micro-controlers are not multicore based, this should not be
 * a problem.
 */


#ifndef __FRAMAC__

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
    .state = SCSI_IDLE
};

static cdb_t queued_cdb = { 0 };
#endif

#ifdef __FRAMAC__
/* In FramaC mode, the scsi_ctx symbol is visible (as defined in a header to allow its usage in ACSL declaration).
 * Nevertheless, WP consider it as static and any modification out of this object will not impact the symbol value used here.
 * To correct this, a dedicated getter for this symbol is written here to export the correct symbol value to the EVA entrypoint.
 * This permits to handle correct settings of the context from entrypoint object file. */

/*@
  @ assigns \nothing;
  @ ensures \result == &scsi_ctx;
  */
scsi_context_t *scsi_get_context(void) {
    return &scsi_ctx;
};
#endif

/*@
  @ requires \separated(&cbw, &scsi_ctx,&GHOST_opaque_drv_privates, &bbb_ctx);
  @ requires sensekey < 0xff;
  @ assigns scsi_ctx.error,
            GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.state;
  @ ensures scsi_ctx.state == SCSI_IDLE;
  */
#ifndef __FRAMAC__
static
#endif
void scsi_error(uint16_t sensekey, uint8_t asc, uint8_t ascq)
{
    log_printf("%s: %s: status=%d\n", __func__, __func__, sensekey);
    log_printf("%s: state -> Error\n", __func__);
    uint32_t err = 0;

    /* @ assert sensekey <= 0xff; */
    err = (uint32_t)
        ((sensekey & 0xff) << 16 |
         asc << 8       |
         ascq);
    scsi_ctx.error = err;
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
/*@
  @ assigns \nothing;
  */
#ifndef __FRAMAC__
static inline
#endif
mbed_error_t enter_critical_section(void)
{
    uint8_t ret;
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* this is a syscall requiring the kernel to lock ISR for a short time */
    ret = sys_lock(LOCK_ENTER); /* Enter in critical section */
    if (ret != SYS_E_DONE) {
        log_printf("%s: Error: failed entering critical section!\n", __func__);
        errcode = MBED_ERROR_BUSY;
    }
    return errcode;
}

/*
 * \brief leaving a critical section
 *
 * Reallow the execution of the previously postponed task ISR.
 */
/*@
  @ assigns \nothing;
  */
#ifndef __FRAMAC__
static inline
#endif
void leave_critical_section(void)
{
    sys_lock(LOCK_EXIT);        /* Exit from critical section, should not
                                   fail */
    return;
}

/********* About debugging and pretty printing **************/

#if SCSI_DEBUG
/* Frama-C info: not required here as out of Frama-C proof */
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

/*@
  @ assigns \nothing;
  */
#ifndef __FRAMAC__
static inline
#endif
bool scsi_is_ready_for_data_receive(void)
{
    return ((scsi_ctx.direction == SCSI_DIRECTION_RECV
             || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY);
}

/*
 * Is the current context compatible with data transmission ?
 */
/*@
  @ assigns \nothing;
  */
#ifndef __FRAMAC__
static inline
#endif
bool scsi_is_ready_for_data_send(void)
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
/*@
  @ requires \separated(buffer + (0 .. size-1),&scsi_ctx,&cbw, &bbb_ctx,&GHOST_opaque_drv_privates);
  @ assigns scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.line_state,GHOST_opaque_drv_privates, bbb_ctx.state;

  // due to FramaC call to scsi_data_vailable()
  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, scsi_ctx.size_to_process, scsi_ctx.state;

  @ behavior invbuffer:
  @    assumes buffer == NULL;
  @    ensures scsi_ctx.addr == \old(scsi_ctx.addr);
  @    ensures scsi_ctx.direction == \old(scsi_ctx.direction);
  @    ensures scsi_ctx.line_state == \old(scsi_ctx.line_state);
  @    ensures GHOST_opaque_drv_privates == \old(GHOST_opaque_drv_privates);
  @    ensures bbb_ctx.state == \old(bbb_ctx.state);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior sizenull:
  @    assumes buffer != NULL;
  @    assumes size == 0;
  @    ensures scsi_ctx.addr == \old(scsi_ctx.addr);
  @    ensures scsi_ctx.direction == \old(scsi_ctx.direction);
  @    ensures scsi_ctx.line_state == \old(scsi_ctx.line_state);
  @    ensures GHOST_opaque_drv_privates == \old(GHOST_opaque_drv_privates);
  @    ensures bbb_ctx.state == \old(bbb_ctx.state);
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior ok:
  @    requires \valid(buffer + (0 .. size-1));
  @    requires size > 0;
  @    ensures scsi_ctx.direction == SCSI_DIRECTION_RECV;
  @    ensures scsi_ctx.line_state == SCSI_TRANSMIT_LINE_BUSY;
  @    ensures scsi_ctx.addr == 0; // usb_bbb_recv() postconditions are set in usb_bbb_recv() function contract
  @    ensures \result == MBED_ERROR_NONE;

  @ complete behaviors;
  @ disjoint behaviors;

 */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_get_data(uint8_t *buffer, uint32_t size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
#if SCSI_DEBUG > 1
    log_printf("%s: size: %d \n", __func__, size);
#endif
    if (buffer == NULL) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (size == 0) {
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
     * received data.
     * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
     * by the driver outep interrupt in DATA mode.
     * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
     * this trigger, instead of waiting for its asyncrhonous execution.
     */
#ifdef __FRAMAC__
    if (!scsi_is_ready_for_data_receive()) {
        /* emulating asynchronous trigger */
        scsi_data_available(scsi_ctx.global_buf_len);
    }
#else
    while (!scsi_is_ready_for_data_receive()) {
        request_data_membarrier();
        continue;
    }
#endif

    set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_RECV);

    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_BUSY);
    scsi_ctx.addr = 0;
    request_data_membarrier();

    usb_bbb_recv(buffer, size);
err:
    return errcode;
}

/*
 * Request to send data of given size into the BULK stack.
 * This function is sending an asynchronous write request. The
 * transmission terminaison is acknowledge by a trigger on scsi_data_sent()
 */
/*@
  @ requires \separated(data + (0 .. size-1),&scsi_ctx,&cbw, &bbb_ctx,&GHOST_opaque_drv_privates);
  @ assigns scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.line_state,GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state;
 */
void scsi_send_data(uint8_t *data, uint32_t size)
{
#if SCSI_DEBUG > 1
    log_printf("%s: size: %d \n", __func__, size);
#endif

    set_u8_with_membarrier(&scsi_ctx.direction, SCSI_DIRECTION_SEND);
    set_u8_with_membarrier(&scsi_ctx.line_state, SCSI_TRANSMIT_LINE_BUSY);
    scsi_ctx.addr = 0;

    usb_bbb_send(data, size);
}

/*
 * Trigger on input data available
 */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates,&scsi_ctx);
  @ requires \valid_read(bbb_ctx.iface.eps + (0 .. 1));

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;

  @ behavior buffer_bigger_than_sizetoprocess:
  @   assumes (size < scsi_ctx.size_to_process);
  @   ensures scsi_ctx.size_to_process == (\old(scsi_ctx.size_to_process) - \old(size));
  @   ensures scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY;
  @   ensures scsi_ctx.direction == \old(scsi_ctx.direction);
  @   ensures GHOST_opaque_drv_privates == \old(GHOST_opaque_drv_privates);
  @   ensures bbb_ctx.state == \old(bbb_ctx.state);
  @   ensures scsi_ctx.state == \old(scsi_ctx.state);

  @ behavior size_smaller_than_buffer:
  @   assumes (size >= scsi_ctx.size_to_process);
  @   ensures scsi_ctx.size_to_process == 0;
  @   ensures scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY;
  @   ensures scsi_ctx.direction == SCSI_DIRECTION_IDLE;
  @   ensures scsi_ctx.state == SCSI_IDLE;

  @ complete behaviors;
  @ disjoint behaviors;

  */
#ifndef __FRAMAC__
static
#endif
void scsi_data_available(uint32_t size)
{
#if SCSI_DEBUG > 1
    /* this function is triggered, printing trigger events is done only
     * on debug level 2 */
    log_printf("%s: %d\n", __func__, size);
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
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates,&scsi_ctx);
  @ requires \valid_read(bbb_ctx.iface.eps + (0 .. 1));

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;

  @ behavior size_bigger_than_buffer:
  @   assumes (scsi_ctx.size_to_process > scsi_ctx.global_buf_len);
  @   ensures scsi_ctx.size_to_process == (\old(scsi_ctx.size_to_process) - \old(scsi_ctx.global_buf_len));
  @   ensures scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY;
  @   ensures scsi_ctx.direction == \old(scsi_ctx.direction);
  @   ensures GHOST_opaque_drv_privates == \old(GHOST_opaque_drv_privates);
  @   ensures bbb_ctx.state == \old(bbb_ctx.state);
  @   ensures scsi_ctx.state == \old(scsi_ctx.state);

  @ behavior size_smaller_than_buffer:
  @   assumes (scsi_ctx.size_to_process <= scsi_ctx.global_buf_len);
  @   ensures scsi_ctx.size_to_process == 0;
  @   ensures scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY;
  @   ensures scsi_ctx.direction == SCSI_DIRECTION_IDLE;
  @   ensures scsi_ctx.state == SCSI_IDLE;

  @ complete behaviors;
  @ disjoint behaviors;

  */
#ifndef __FRAMAC__
static
#endif
void scsi_data_sent(void)
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


/*@
  @ requires \separated(&cbw, response, &bbb_ctx,&GHOST_opaque_drv_privates,&scsi_ctx);
  @ requires \valid_read(response);
  @ assigns *response;
  */
#ifndef __FRAMAC__
static
#endif
void scsi_forge_mode_sense_response(u_mode_parameter * response,
                                           uint8_t mode)
{
    if (mode == SCSI_CMD_MODE_SENSE_6) {
#ifndef __FRAMAC__
        /* FIXME: this should be, in FramaC, also done */
        memset(response, 0x0, sizeof(mode_parameter6_data_t));
#endif
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
#ifndef __FRAMAC__
        /* FIXME: this should be, in FramaC, also done */
        memset(response, 0x0, sizeof(mode_parameter10_data_t));
#endif
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
/* XXX: we should use memory barriers instead of volatile here */
extern volatile bool reset_requested;
#endif


/*
 * Enqueue any received SCSI command
 * this function is executed in a handler context when a command comes from USB.
 */


/*@
  @ requires cdb_len <= sizeof(cdb_t);
  @ requires \valid_read(cdb + (0 .. cdb_len-1));
  @ requires \separated(((uint8_t*)&queued_cdb + (0 .. cdb_len-1)), &scsi_ctx, &cdb[0 .. cdb_len-1], &reset_requested);
  @ assigns scsi_ctx.queue_empty, queued_cdb;

  @ behavior reset_req:
  @    assumes reset_requested == \true;
  @    ensures scsi_ctx.queue_empty == \true;

  @ behavior ok:
  @    assumes reset_requested != \true;
  @    ensures scsi_ctx.queue_empty == \false;
  //@    ensures \forall integer i; 0 <= i < cdb_len ==> ((uint8_t*)queued_cdb)[i] == cdb[i];

  @ complete behaviors;
  @ disjoint behaviors;

 */
#ifndef __FRAMAC__
static
#endif
void scsi_parse_cdb(uint8_t *cdb, uint8_t cdb_len)
{
    if (reset_requested == true) {
        /* a cdb is received while the main thread as not yet cleared the reset trigger */
        /* waiting for main thread to clear reset trigger */
        set_bool_with_membarrier(&scsi_ctx.queue_empty, true);
        request_data_membarrier();
        goto err;
    }
    /*@ assert cdb_len ≤ sizeof(queued_cdb); */

    /* Only up to 16 bytes commands are supported: bigger commands are truncated,
     * See cdb_t definition in scsi_cmd.h */
#ifdef __FRAMAC__
    /* INFO: here, we substitute the memcpy call with a local copy to
     * validate the assign constraint. Thus, the result (fonction postconditions)
     * is exactly the same. */
    uint8_t *queued_gen = (uint8_t*)&queued_cdb;
    /*@ assert \valid(queued_gen+(0..sizeof(cdb_t)-1)); */
    /*@ assert cdb_len <= sizeof(cdb_t); */

    FC_memcpy_u8(queued_gen, cdb, cdb_len);
    /* assert \forall integer i; 0 <= i < cdb_len ==> queued_gen[i] == cdb[i]; */
#else
    memcpy((void *) &queued_cdb, (void *) cdb, cdb_len);
    request_data_membarrier();
#endif
    set_bool_with_membarrier(&scsi_ctx.queue_empty, false);
err:
    return;
}


/*
 * Commands implementation.
 *
 * All commands implementation check the SCSI state automaton to validate that
 * the transition is authorized, and then execute the command.
 */

/* SCSI_CMD_INQUIRY */

/*@
  @ requires \valid_read(cdb);
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, cdb, &scsi_ctx);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;
  @ assigns scsi_ctx.error, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state,
            bbb_ctx.state, scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NONE || \result == MBED_ERROR_INVPARAM);


  @ disjoint behaviors;
  @ complete behaviors;
  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_inquiry(scsi_state_t  current_state, cdb_t const * const cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    inquiry_data_t response = { 0 };
    cdb6_inquiry_t const * inq;
    uint8_t next_state;

    log_printf("%s:\n", __func__);
    /* Sanity check and next state detection */

    if (!scsi_is_valid_transition(current_state, SCSI_CMD_INQUIRY)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }

    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_INQUIRY);
    /* @ assert next_state == SCSI_IDLE; */
    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    inq = &(cdb->payload.cdb6_inquiry);


#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(cdb, SCSI_CMD_INQUIRY);
#endif

    uint16_t alen = ntohs(inq->allocation_length);

    /* sanitize received cmd in conformity with SCSI standard */
    if (inq->EVPD == 0 && alen < 5) {
        /* invalid: additional fields parameter can't be send */
        /*@ assert is_invalid_inquiry(&(cdb->payload.cdb6_inquiry)); */
        goto invalid_cmd;
    }

    if (inq->EVPD == 1 && alen < 4) {
        /* invalid: additional fields parameter can't be send */
        /*@ assert is_invalid_inquiry(&(cdb->payload.cdb6_inquiry)); */
        goto invalid_cmd;
    }


    /*@ assert !is_invalid_inquiry(&(cdb->payload.cdb6_inquiry)); */

    /* Most of support bits are set to 0
     * version is 0 because the device does not claim conformance to any
     * standard
     */
    response.periph_device_type = 0x0;  /* direct access block device */
    response.RMB = 1;           /* Removable media */

    response.data_format = 2;   /* < 2 obsoletes, > 2 reserved */
    response.additional_len = sizeof(response) - 5;     /* (36 - 5) bytes after this one remain */
    response.additional_len = sizeof(response) - 5;     /* (36 - 5) bytes after this one remain */

#ifdef __FRAMAC__
    FC_memset_ch(response.vendor_info, 0x20, sizeof(response.vendor_info));
    FC_memcpy_ch(response.vendor_info, CONFIG_USB_DEV_MANUFACTURER,
           strlen(CONFIG_USB_DEV_MANUFACTURER));
    FC_memset_ch(response.product_identification, 0x20,
           sizeof(response.product_identification));
    FC_memcpy_ch(response.product_identification, CONFIG_USB_DEV_PRODNAME,
           strlen(CONFIG_USB_DEV_PRODNAME));
    FC_memcpy_ch(response.product_revision, CONFIG_USB_DEV_REVISION,
           strlen(CONFIG_USB_DEV_REVISION));
#else
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
#endif
    log_printf("%s: %s\n", __func__, response.product_revision);


    if (inq->allocation_length > 0) {
        usb_bbb_send((uint8_t *) & response,
                     (alen < sizeof(response)) ? alen : sizeof(response));
    } else {
        log_printf("allocation length is 0\n");
    }
    return errcode;

 invalid_cmd:
    log_printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVPARAM;
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}

/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;
  @ requires \valid_read(current_cdb);

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.state ;
  @ ensures \result == MBED_ERROR_NONE;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_prevent_allow_medium_removal(scsi_state_t current_state,
                                                          cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* no invalid transition as this CMD is allowed in both IDLE & ERROR states */

    next_state = scsi_next_state(current_state, SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL);
    scsi_set_state(next_state);

    log_printf("%s: Prevent allow medium removal: %x\n", __func__,
           current_cdb->payload.cdb10_prevent_allow_removal.prevent);
    /* TODO: Add callback ? */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);

    return errcode;
    /* effective transition execution (if needed) */
}

/*@
  @ requires \separated(&cbw, current_cdb, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.error, scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NONE || \result == MBED_ERROR_NOBACKEND);


  @ disjoint behaviors;
  @ complete behaviors;


  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_read_format_capacities(scsi_state_t current_state,
                                                         cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;


    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_READ_FORMAT_CAPACITIES)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }

    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_READ_FORMAT_CAPACITIES);
    /* @ assert next_state == SCSI_IDLE; */
    scsi_set_state(next_state);

    cdb12_read_format_capacities_t *rfc =
        &(current_cdb->payload.cdb12_read_format_capacities);

    uint32_t storage_size = scsi_ctx.storage_size;
    if (storage_size == 0) {
        /* This should not happend in a nominal way (i.e. should have been set previously */
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                ASCQ_NO_ADDITIONAL_SENSE);
        errcode = MBED_ERROR_NOBACKEND;
        goto end;
    }

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
end:
    return errcode;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;

}


/*
 * SCSI_CMD_READ_6
 * INFO: this command is deprecated but is implemented for retrocompatibility
 * with older Operating Systems
 */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  // this assign line is the consequence of the synchronized scsi_data_sent() trigger (instead of async one)
  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVPARAM);


  @ disjoint behaviors;
  @ complete behaviors;



  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_read_data6(scsi_state_t current_state, cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;
    uint8_t next_state;
    mbed_error_t error;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_READ_6)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_READ_6);
    /* @ assert next_state == SCSI_IDLE; */

    /* entering READ state... */
    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        errcode = MBED_ERROR_NOSTORAGE;
        goto end;
    }

    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t)(current_cdb->payload.cdb6.logical_block & 0xffff))
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


    /*@
      @ loop invariant \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, current_cdb, &scsi_ctx);
      @ loop invariant scsi_ctx.size_to_process >= 0;
      @ loop assigns num_sectors, rw_lba, error, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state,
            scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.error, scsi_ctx.state;
      */
    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        error = scsi_storage_backend_read(rw_lba, num_sectors);
        if (error == MBED_ERROR_RDERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        /* send data we have just read */
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* check for unsigned overflow */
        uint32_t logicalblock_increment = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        if ((UINT32_MAX - rw_lba) < logicalblock_increment) {
            /* uint32 overflow detected! */
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_INVPARAM;
            goto end;
        }
        /* increment read pointer */
        /*@ assert ((uint64_t)logicalblock_increment + (uint64_t)rw_lba <= UINT32_MAX); */
        rw_lba += logicalblock_increment;
        /* active wait for data to be sent */
        /* here, we wait for an asyncrhonous execution of a trigger setting the IN EP as ready.
         * This trigger is scsi_data_sent(), which is executed when all the previously data
         * configured to be send has been transmitted to the host.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_send()) {
            /* previous scsi_send_data() finished to be sent by the core (this should be an async trap in nominal mode) */
            scsi_data_sent();
        }
#else
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
#endif
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
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* active wait for data to be sent */
        /* here, we wait for an asyncrhonous execution of a trigger setting the IN EP as ready.
         * This trigger is scsi_data_sent(), which is executed when all the previously data
         * configured to be send has been transmitted to the host.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_send()) {
            /* previous scsi_send_data() finished to be sent by the core (this should be an async trap in nominal mode) */
            scsi_data_sent();
        }
#else
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
#endif
    }

 end:
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}


/* SCSI_CMD_READ_10 */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  // this assign line is the consequence of the synchronized scsi_data_sent() trigger (instead of async one)
  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVPARAM);


  @ disjoint behaviors;
  @ complete behaviors;



  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_read_data10(const scsi_state_t current_state,
                                         cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;
    uint8_t next_state;

    mbed_error_t error;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_READ_10)) {
        /* @ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_READ_10);
    /* @ assert next_state == SCSI_IDLE; */

    /* entering READ state... */
    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        log_printf("read capcity not yet set\n");
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        errcode = MBED_ERROR_NOSTORAGE;
        goto end;
    }

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

    /*@
      @ loop invariant \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, current_cdb, &scsi_ctx);
      @ loop invariant scsi_ctx.size_to_process >= 0;
      @ loop assigns num_sectors, rw_lba, error, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state,
            scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.error, scsi_ctx.state;
      */
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
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* check for unsigned overflow */
        uint32_t logicalblock_increment = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        if ((UINT32_MAX - rw_lba) < logicalblock_increment) {
            /* increment will generate overflow ! This should not happen as logical blocks of
             * 512 bytes should not exceed U32_MAX */
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_UNRECOVERED_READ_ERROR,
                    ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_INVPARAM;
            goto end;

        }
        /* increment read pointer */
        /*@ assert ((uint64_t)logicalblock_increment + (uint64_t)rw_lba <= UINT32_MAX); */
        rw_lba += logicalblock_increment;
        /* active wait for data to be sent */
        /* here, we wait for an asyncrhonous execution of a trigger setting the IN EP as ready.
         * This trigger is scsi_data_sent(), which is executed when all the previously data
         * configured to be send has been transmitted to the host.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_send()) {
            /* previous scsi_send_data() finished to be sent by the core (this should be an async trap in nominal mode) */
            scsi_data_sent();
        }
#else
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
#endif
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
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* active wait for data to be sent */
        /* here, we wait for an asyncrhonous execution of a trigger setting the IN EP as ready.
         * This trigger is scsi_data_sent(), which is executed when all the previously data
         * configured to be send has been transmitted to the host.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_send()) {
            /* previous scsi_send_data() finished to be sent by the core (this should be an async trap in nominal mode) */
            scsi_data_sent();
        }
#else
        while (!scsi_is_ready_for_data_send()) {
            request_data_membarrier();
            continue;
        }
#endif
    }
 end:
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
            ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}


/* SCSI_CMD_READ_CAPACITY_10 */
/*@
  @ requires \separated(current_cdb, &cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state,
            bbb_ctx.state, scsi_ctx.state,
            scsi_ctx.storage_size,scsi_ctx.block_size, scsi_ctx.error,
            scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_NONE);


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_read_capacity10(scsi_state_t current_state,
                                             cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;
    read_capacity10_parameter_data_t response;
    uint8_t ret;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */

    if (!scsi_is_valid_transition(current_state, SCSI_CMD_READ_CAPACITY_10)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_READ_CAPACITY_10);
    /* @ assert next_state == SCSI_IDLE; */


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
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (10) */

    response.ret_lba = htonl(scsi_ctx.storage_size - 1);
    response.ret_block_length = htonl(scsi_ctx.block_size);

    usb_bbb_send((uint8_t *) & response,
                 sizeof(read_capacity10_parameter_data_t));
err:
    return errcode;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}

/* SCSI_CMD_READ_CAPACITY_16 */
/*@
  @ requires \separated(current_cdb, &cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state,
            bbb_ctx.state, scsi_ctx.state,
            scsi_ctx.storage_size,scsi_ctx.block_size, scsi_ctx.error,
            scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures (\result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE);
  @    ensures scsi_ctx.state == SCSI_IDLE;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_read_capacity16(scsi_state_t current_state,
                                             cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;
    read_capacity16_parameter_data_t response;
    cdb16_read_capacity_16_t *rc16;
    uint8_t ret;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_READ_CAPACITY_16)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_READ_CAPACITY_16);
    /* @ assert next_state == SCSI_IDLE; */

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
        errcode = MBED_ERROR_NOSTORAGE;
        goto err;
    }

    /* get back cdb content from union */
    rc16 = &(current_cdb->payload.cdb16_read_capacity);

    /* what is expected is the _LAST_ LBA address ....
     * See Working draft SCSI block cmd  5.10.2 READ CAPACITY (16) */

    /* creating response... */
#ifndef __FRAMAC__
    memset((void *) &response, 0x0, sizeof(read_capacity16_parameter_data_t));
#endif
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
err:
    return errcode;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}


/* SCSI_CMD_REPORT_LUNS */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, scsi_ctx.state, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior badinput:
  @    assumes current_state == SCSI_IDLE;
  @    assumes is_invalid_report_luns(&current_cdb->payload.cdb12_report_luns);
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    assumes !is_invalid_report_luns(&current_cdb->payload.cdb12_report_luns);
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE;


  @ disjoint behaviors;
  @ complete behaviors;


  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_report_luns(scsi_state_t current_state,
                                         cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;
    cdb12_report_luns_t *rl;
    bool    check_condition = false;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_REPORT_LUNS)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }


    rl = &(current_cdb->payload.cdb12_report_luns);

    if (ntohl(rl->allocation_length) < 16) {
        /* invalid: requested to be at least 16 by standard */
        goto invalid_cmd;
    }

    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_REPORT_LUNS);
    /* @ assert next_state == SCSI_IDLE; */

    scsi_set_state(next_state);

    if (ntohl(rl->allocation_length) < 24) {
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
                 (ntohl(rl->allocation_length) <
                  sizeof(response)) ? ntohl(rl->
                                            allocation_length) :
                 sizeof(response));

    /* if the host didn't reserve enough space to respond, inform it that
     * some informations are missing */
    if (check_condition) {
        usb_bbb_send_csw(SCSI_STATUS_CHECK_CONDITION, 0);
    }
    return errcode;

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
    errcode = MBED_ERROR_INVPARAM;
    return errcode;


 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}

/* SCSI_CMD_REQUEST_SENSE */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, scsi_ctx.state, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;
  @ ensures \result == MBED_ERROR_NONE;
  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_request_sense(scsi_state_t current_state,
                                           cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;
    request_sense_parameter_data_t data = { 0 };

    log_printf("%s\n", __func__);

    /* @ assert SCSI_IDLE <= current_state <= SCSI_ERROR; */
    next_state = scsi_next_state(current_state, SCSI_CMD_REQUEST_SENSE);
    /* @ assert next_state == SCSI_IDLE; */

    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    log_printf("%s: desc: %x, allocation_length: %x\n",
           current_cdb->payload.cdb10_request_sense.desc,
           current_cdb->payload.cdb10_request_sense.allocation_length);
#endif

    /* TODO If desc is set to 1 and descriptor format sense data is supported */

    /* descriptor format sense data shall be returned. */

    data.error_code = 0x70;
    data.sense_key = scsi_error_get_sense_key(scsi_ctx.error);
    data.additional_sense_length = 0x0a;
    data.asc = scsi_error_get_asc(scsi_ctx.error);
    data.ascq = scsi_error_get_ascq(scsi_ctx.error);
    /* now that data has been sent successfully, scsi error is cleared */
    scsi_ctx.error = 0;

    usb_bbb_send((uint8_t *) & data, sizeof(data));
    return errcode;
}



/* SCSI_CMD_MODE_SENSE(10) */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;
  @ ensures \result == MBED_ERROR_NONE;
  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_mode_sense10(scsi_state_t current_state,
                                          cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* @ assert SCSI_IDLE <= current_state <= SCSI_ERROR; */
    next_state = scsi_next_state(current_state, SCSI_CMD_MODE_SENSE_10);
    /* @ assert next_state == SCSI_IDLE; */
    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    /* Sending Mode Sense 10 answer */
    u_mode_parameter response = { 0 };

    scsi_forge_mode_sense_response(& response,
                                   SCSI_CMD_MODE_SENSE_10);
    /* Sending Mode Sense 10 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *) & response.mode10, sizeof(mode_parameter10_data_t));

    return errcode;
}


/* SCSI_CMD_MODE_SENSE(6) */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;


  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;
  @ ensures \result == MBED_ERROR_NONE;
  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_mode_sense6(scsi_state_t current_state,
                                         cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    next_state = scsi_next_state(current_state, SCSI_CMD_MODE_SENSE_6);
    scsi_set_state(next_state);

#if SCSI_DEBUG > 1
    scsi_debug_dump_cmd(current_cdb, SCSI_CMD_MODE_SENSE_10);
#endif

    u_mode_parameter response = { 0 };

    scsi_forge_mode_sense_response(& response,
                                   SCSI_CMD_MODE_SENSE_6);
    /* Sending Mode Sense 6 answer */

    /*usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t)); */
    usb_bbb_send((uint8_t *) & response, sizeof(mode_parameter6_data_t));
    return errcode;
}

/* SCSI_CMD_MODE_SELECT(6) */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_mode_select6(scsi_state_t current_state,
                                          cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_MODE_SELECT_6)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_MODE_SELECT_6);
    /* @ assert next_state == SCSI_IDLE; */
    scsi_set_state(next_state);

    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}


/* SCSI_CMD_MODE_SELECT(10) */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_mode_select10(scsi_state_t current_state,
                                           cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_MODE_SELECT_10)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_MODE_SELECT_10);
    /* @ assert next_state == SCSI_IDLE; */
    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    /* @ assert bbb_ctx.state == USB_BBB_STATE_STATUS; */
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}


/* SCSI_CMD_TEST_UNIT_READY */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_cmd_test_unit_ready(scsi_state_t current_state,
                                             cdb_t * current_cdb __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint8_t next_state;

    log_printf("%s\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_TEST_UNIT_READY)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_TEST_UNIT_READY);
    /* @ assert next_state == SCSI_IDLE; */

    scsi_set_state(next_state);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}

/*
 * SCSI_CMD_WRITE(6)
 * This command is declared as obsolete by the T10 consorsium.
 * It is implemented here for retrocompatibility with old Operating System
 */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_opaque_drv_privates, bbb_ctx.state ;
  // below is the consequence of synchronous call to scsi_data_available() in waiting loop
  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;


  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVPARAM;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_write_data6(scsi_state_t current_state, cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;
    uint8_t next_state;

    log_printf("%s:\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_WRITE_6)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_WRITE_6);
    /* @ assert next_state == SCSI_IDLE; */

    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        errcode = MBED_ERROR_NOSTORAGE;
        goto end;
    }


    /* TODO: is the big endian is set only on the last 16 bytes of this
     * unaligned field ? */
    rw_lba = ntohs((uint16_t)(current_cdb->payload.cdb6.logical_block & 0xffff))
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

    /*@
      @ loop invariant \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, current_cdb, &scsi_ctx);

      @ loop assigns num_sectors, error, rw_lba,
                     scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.line_state,GHOST_opaque_drv_privates, bbb_ctx.state,
                     GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, scsi_ctx.size_to_process, scsi_ctx.state;
      */
    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* Wait until we have indeed received data from the USB lower layers */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while (scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            request_data_membarrier();
            continue;
        }
#endif
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                    ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        uint32_t logicalblock_increment = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        if ((UINT32_MAX - rw_lba) < logicalblock_increment) {
            /* uint32 overflow detected! */
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_INVPARAM;
            goto end;
        }
        rw_lba += logicalblock_increment;
        /* wait for async event making current state ready to recv */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_receive()) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
#endif
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        /* Wait until we have indeed received data from the USB lower layers */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
            request_data_membarrier();
            continue;
        }
#endif
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                    ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        /* wait for async event making current state ready to recv */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_receive()) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
#endif
    }
 end:
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
               ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}



/* SCSI_CMD_WRITE(10) */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires \valid_read(current_cdb);
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_opaque_drv_privates, bbb_ctx.state ;
  // below is the consequence of synchronous call to scsi_data_available() in waiting loop
  @ assigns GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, scsi_ctx.size_to_process, scsi_ctx.line_state, scsi_ctx.direction, scsi_ctx.state;

  @ behavior badstate:
  @    assumes current_state != SCSI_IDLE;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes current_state == SCSI_IDLE;
  @    ensures scsi_ctx.state == SCSI_IDLE;
  @    ensures \result == MBED_ERROR_NONE || \result == MBED_ERROR_NOSTORAGE || \result == MBED_ERROR_INVPARAM;


  @ disjoint behaviors;
  @ complete behaviors;

  */
#ifndef __FRAMAC__
static
#endif
mbed_error_t scsi_write_data10(scsi_state_t current_state, cdb_t * current_cdb)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    mbed_error_t error;
    uint8_t next_state;

    log_printf("%s:\n", __func__);

    /* Sanity check and next state detection */
    if (!scsi_is_valid_transition(current_state, SCSI_CMD_WRITE_10)) {
        /*@ assert current_state != SCSI_IDLE; */
        goto invalid_transition;
    }
    /* @ assert current_state == SCSI_IDLE; */
    next_state = scsi_next_state(current_state, SCSI_CMD_WRITE_10);
    /* @ assert next_state == SCSI_IDLE; */

    scsi_set_state(next_state);

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                   ASCQ_NO_ADDITIONAL_SENSE);
        errcode = MBED_ERROR_NOSTORAGE;
        goto end;
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

    /*@
      @ loop invariant \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, current_cdb, &scsi_ctx);

      @ loop assigns num_sectors, error, rw_lba,
                     scsi_ctx.addr, scsi_ctx.direction, scsi_ctx.line_state,GHOST_opaque_drv_privates, bbb_ctx.state,
                     GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, scsi_ctx.size_to_process, scsi_ctx.state;
      */
    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* Wait until we have indeed received data from the USB lower layers */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */

#ifdef __FRAMAC__
        if (scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            request_data_membarrier();
            continue;
        }
#endif
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                    ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        uint32_t logicalblock_increment = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        if ((UINT32_MAX - rw_lba) < logicalblock_increment) {
            /* uint32 overflow detected! */
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_INVPARAM;
            goto end;
        }
        rw_lba += logicalblock_increment;
        /* here, we wait for an asyncrhonous execution of a trigger setting the IN EP as ready.
         * This trigger is scsi_data_sent(), which is executed when all the previously data
         * configured to be send has been transmitted to the host.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_receive()) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
#endif
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        /* Wait until we have indeed received data from the USB lower layers */
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while(scsi_ctx.line_state != SCSI_TRANSMIT_LINE_READY){
            request_data_membarrier();
            continue;
        }
#endif
        error = scsi_storage_backend_write(rw_lba, num_sectors);
        if (error == MBED_ERROR_WRERROR) {
            scsi_error(SCSI_SENSE_MEDIUM_ERROR, ASC_WRITE_ERROR,
                       ASCQ_NO_ADDITIONAL_SENSE);
            errcode = MBED_ERROR_NOSTORAGE;
            goto end;
        }
        /* here, we wait for an asyncrhonous execution of a trigger setting the OUT EP as having
         * received data.
         * This trigger is scsi_data_available(), which is executed when the bbb stack is triggered
         * by the driver outep interrupt in DATA mode.
         * Using FramaC, we can't emulate multithreaded execution, so we synchronously execute
         * this trigger, instead of waiting for its asyncrhonous execution.
         */
#ifdef __FRAMAC__
        if (!scsi_is_ready_for_data_receive()) {
            /* emulating asynchronous trigger */
            scsi_data_available(scsi_ctx.global_buf_len);
        }
#else
        while (!scsi_is_ready_for_data_receive()) {
            request_data_membarrier();
            continue;
        }
#endif
    }
 end:
    return errcode;

 invalid_transition:
    log_printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
            ASCQ_NO_ADDITIONAL_SENSE);
    errcode = MBED_ERROR_INVSTATE;
    return errcode;
}

/*@
  @ requires \separated(&bbb_ctx,&GHOST_opaque_drv_privates);
  @ requires \valid_read(bbb_ctx.iface.eps + (0 .. 1));
  @ assigns bbb_ctx.state, GHOST_opaque_drv_privates;
  */
mbed_error_t scsi_initialize_automaton(void)
{
    /* read first command */
    read_next_cmd();
    return MBED_ERROR_NONE;
}

/*
 * SCSI Automaton execution
 */
/*@
  @ requires \separated(&cbw, &bbb_ctx,&GHOST_opaque_drv_privates, &scsi_ctx);
  @ requires SCSI_IDLE <= scsi_ctx.state <= SCSI_ERROR;

  @ assigns scsi_ctx, GHOST_opaque_drv_privates, bbb_ctx.state, GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num].state, bbb_ctx.state ;

  */
mbed_error_t scsi_exec_automaton(void)
{
    /* local cdb copy */
    cdb_t   local_cdb;
    mbed_error_t errcode = MBED_ERROR_NONE;

    if (scsi_ctx.queue_empty == true) {
        request_data_membarrier();
        goto nothing_to_do;
    }

    /* critical section part. This part of the code is handling
     * the command queue to get back the queued cdb block from it.
     */
    if (enter_critical_section() != MBED_ERROR_NONE) {
        /* unable to enter critical section by now... leaving current turn */
        log_printf("Unable to enter critical section!\n");
        goto nothing_to_do;
    }
#ifdef __FRAMAC__
    /* Here, we use a local memcpy implementation. The resulting execution is the
     * same, but accepted by framaC.
     * We keep the libC memcpy in non-FramaC implementation for performances reasons */
    uint8_t *local_u8_cdb = (uint8_t*)&local_cdb;
    uint8_t *queued_u8_cdb = (uint8_t*)&queued_cdb;
    /*@ assert \valid(queued_u8_cdb+(0..sizeof(cdb_t)-1)); */
    /*@ assert \valid(local_u8_cdb+(0..sizeof(cdb_t)-1)); */

    FC_memcpy_u8(local_u8_cdb, queued_u8_cdb, sizeof(cdb_t));
#else
    memcpy((void *) &local_cdb, (void *) &queued_cdb, sizeof(cdb_t));
#endif
    /* we handle a signe command at a time, which is standard for the
     * SCSI automaton, as SCSI is syncrhonous */
    set_bool_with_membarrier(&scsi_ctx.queue_empty, true);

    leave_critical_section();
    /* end of the critical section part. From now one, ISR can
     * be executed again
     */

    scsi_state_t current_state = scsi_get_state();
    /*@ assert SCSI_IDLE <= current_state <= SCSI_ERROR; */

    switch (local_cdb.operation) {
        case SCSI_CMD_INQUIRY:
            errcode = scsi_cmd_inquiry(current_state, &local_cdb); // ghost(alloc_len) */;
            break;

        case SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL:
            errcode = scsi_cmd_prevent_allow_medium_removal(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_6:
            errcode = scsi_cmd_read_data6(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_10:
            errcode = scsi_cmd_read_data10(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_CAPACITY_10:
            errcode = scsi_cmd_read_capacity10(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_CAPACITY_16:
            errcode = scsi_cmd_read_capacity16(current_state, &local_cdb);
            break;

        case SCSI_CMD_REPORT_LUNS:
            errcode = scsi_cmd_report_luns(current_state, &local_cdb);
            break;

        case SCSI_CMD_READ_FORMAT_CAPACITIES:
            errcode = scsi_cmd_read_format_capacities(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SELECT_10:
            errcode = scsi_cmd_mode_select10(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SELECT_6:
            errcode = scsi_cmd_mode_select6(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SENSE_10:
            errcode = scsi_cmd_mode_sense10(current_state, &local_cdb);
            break;

        case SCSI_CMD_MODE_SENSE_6:
            errcode = scsi_cmd_mode_sense6(current_state, &local_cdb);
            break;


        case SCSI_CMD_REQUEST_SENSE:
            errcode = scsi_cmd_request_sense(current_state, &local_cdb);
            break;
#if 0
        /* not yet supported */
        case SCSI_CMD_SEND_DIAGNOSTIC:
            scsi_cmd_send_diagnostic(current_state, &local_cdb);
            break;
#endif
        case SCSI_CMD_TEST_UNIT_READY:
            errcode = scsi_cmd_test_unit_ready(current_state, &local_cdb);
            break;

        case SCSI_CMD_WRITE_6:
            errcode = scsi_write_data6(current_state, &local_cdb);
            break;

        case SCSI_CMD_WRITE_10:
            errcode = scsi_write_data10(current_state, &local_cdb);
            break;

        default:
            log_printf("%s: Unsupported command: %x  \n", __func__,
                   local_cdb.operation);
            scsi_error(SCSI_SENSE_ILLEGAL_REQUEST, ASC_NO_ADDITIONAL_SENSE,
                       ASCQ_NO_ADDITIONAL_SENSE);
            break;
    };

 nothing_to_do:
    return errcode;
}


/*
 * Resetting SCSI context. Should be executed as a trigger of BULK level
 * USB reset order
 */
/*@
  @ requires \separated(&scsi_ctx);
  @ assigns scsi_ctx;
  */
#ifndef __FRAMAC__
static
#endif
void scsi_reset_context(void)
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

/*@
  @ requires \separated(&scsi_ctx, &bbb_ctx, buf + (0..len-1), &cbw);
  @ assigns scsi_ctx, bbb_ctx;

  @ behavior invbuf:
  @    assumes buf == NULL || len == 0;
  @    ensures \result == MBED_ERROR_INVPARAM;

  @ behavior ok:
  @    assumes buf != NULL && len > 0;
  @    ensures \result == MBED_ERROR_NONE;

  @ disjoint behaviors;
  @ complete behaviors;
  */
mbed_error_t scsi_early_init(uint8_t * buf, uint16_t len)
{

    log_printf("%s\n", __func__);

    if (!buf || len == 0) {
        goto init_error;
    }
    scsi_ctx.direction = SCSI_DIRECTION_IDLE,
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY,
    scsi_ctx.size_to_process = 0,
    scsi_ctx.addr = 0,
    scsi_ctx.error = 0,
    scsi_ctx.queue_empty = true,
    scsi_ctx.global_buf = NULL,
    scsi_ctx.global_buf_len = 0,
    scsi_ctx.block_size = 0,
    scsi_ctx.storage_size = 0,

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
/*@
  @ requires \separated(&scsi_ctx,scsi_ctx.global_buf + (0 .. scsi_ctx.global_buf_len), &GHOST_opaque_drv_privates,&bbb_ctx, ctx_list + (0 .. CONFIG_USBCTRL_FW_MAX_CTX-1));

  @ assigns scsi_ctx, scsi_ctx.global_buf[0 .. scsi_ctx.global_buf_len-1], ctx_list[0 .. CONFIG_USBCTRL_FW_MAX_CTX-1], bbb_ctx.iface, scsi_ctx.state;

  @ behavior invbuf:
  @    assumes scsi_ctx.global_buf == NULL || scsi_ctx.global_buf_len == 0;
  @    ensures \result == MBED_ERROR_INVSTATE;

  @ behavior ok:
  @    assumes scsi_ctx.global_buf != NULL && scsi_ctx.global_buf_len > 0;

  @ disjoint behaviors;
  @ complete behaviors;

  */
mbed_error_t scsi_init(uint32_t usbdci_handler)
{
    uint32_t i;
    mbed_error_t errcode = MBED_ERROR_NONE;
    if (scsi_ctx.global_buf == NULL) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    if (scsi_ctx.global_buf_len == 0) {
        errcode = MBED_ERROR_INVSTATE;
        goto err;
    }
    /*@ assert \valid(scsi_ctx.global_buf+(0..scsi_ctx.global_buf_len-1)); */

    log_printf("%s\n", __func__);

    /* in USB High speed mode, the USB device is mapped (and enabled) just now */
    /* declare interface to libusbctrl  */


    scsi_ctx.storage_size = 0;
    scsi_ctx.block_size = 4096; /* default */

    /*@
      @ loop invariant 0 <= i <= scsi_ctx.global_buf_len;
      @ loop invariant \separated(&scsi_ctx,scsi_ctx.global_buf + (0 .. scsi_ctx.global_buf_len), &GHOST_opaque_drv_privates,&bbb_ctx, ctx_list + (0 .. CONFIG_USBCTRL_FW_MAX_CTX-1));
      @ loop assigns i, scsi_ctx.global_buf[0 .. scsi_ctx.global_buf_len-1];
      @ loop variant scsi_ctx.global_buf_len - i;
      */
    for (i = 0; i < scsi_ctx.global_buf_len; i++) {
        scsi_ctx.global_buf[i] = '\0';
    }

    /* Register our callbacks on the lower layer, declaring iface to
     * usbctrl */
    errcode = usb_bbb_configure(usbdci_handler);
    if (errcode != MBED_ERROR_NONE) {
        goto err;
    }

    scsi_set_state(SCSI_IDLE);

    /* initialize control plane, adding the reset event trigger for SCSI level */

err:
    return errcode;
}

/*@
  @ requires \separated(&scsi_ctx,&GHOST_opaque_drv_privates,&bbb_ctx);
  @ assigns bbb_ctx.state, scsi_ctx;
  */
void scsi_reinit(void)
{
    usb_bbb_reconfigure();
    scsi_reset_context();
}
