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
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/regutils.h"
#include "libusbotghs.h"
#include "libusbctrl.h"
#include "usb_bbb.h"
#include "scsi.h" /* framac content */
#include "libc/syscall.h"
#include "libc/sanhandlers.h"
#include "libc/sync.h"
#include "usb_control_mass_storage.h"


#define BBB_DEBUG CONFIG_USR_LIB_MASSSTORAGE_BBB_DEBUG

#if BBB_DEBUG
# define log_printf(...) printf(__VA_ARGS__)
#else
# define log_printf(...)
#endif



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


#ifndef __FRAMAC__
#define USB_BBB_CBW_SIG		0x43425355      /* "USBC" */

/* Command Block Wrapper */
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

static
#endif
struct scsi_cbw cbw;

#ifdef __FRAMAC__
/* required for ACSL */
extern bool reset_requested;
#endif



/*@
  @ requires \separated(((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)),&bbb_ctx,&usbotghs_ctx);
  @ requires \valid_read(bbb_ctx.iface.eps + (0 .. 1));
  @ assigns bbb_ctx.state, *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx;
  */
void read_next_cmd(void)
{
    log_printf("[USB BBB] %s\n", __func__);
    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_READY);
    usb_backend_drv_set_recv_fifo((uint8_t*)&cbw, sizeof(cbw), bbb_ctx.iface.eps[0].ep_num);
    usb_backend_drv_activate_endpoint(bbb_ctx.iface.eps[0].ep_num, USB_BACKEND_DRV_EP_DIR_OUT);
}

/*@
  @ requires \separated(&cbw, &bbb_ctx);
  @ requires \valid_read(bbb_ctx.iface.eps + (0 .. 1));

  @behavior invinput:
  @   assumes (size != sizeof(cbw) || cbw.sig != USB_BBB_CBW_SIG || cbw.flags.reserved != 0 || cbw.lun.reserved != 0 || cbw.cdb_len.reserved != 0 || cbw.lun.lun != 0);
  @   assigns \nothing;
  @   ensures \result == MBED_ERROR_INVPARAM;

  @behavior ok:
  @   assumes !(size != sizeof(cbw) || cbw.sig != USB_BBB_CBW_SIG || cbw.flags.reserved != 0 || cbw.lun.reserved != 0 || cbw.cdb_len.reserved != 0 || cbw.lun.lun != 0);
  @   assigns *((uint32_t *) (USB_BACKEND_MEMORY_BASE .. USB_BACKEND_MEMORY_END)), usbotghs_ctx, bbb_ctx.tag, bbb_ctx.state, scsi_ctx, queued_cdb, reset_requested;
  @   ensures \result == MBED_ERROR_NONE;
  */
static mbed_error_t usb_bbb_cmd_received(uint32_t size)
{
    mbed_error_t errcode = MBED_ERROR_NONE;
    log_printf("[USB BBB] %s: %dB\n", __func__, size);

    if (size != sizeof(struct scsi_cbw)) {
	    log_printf("[USB BBB] %s: CBW not valid, size %d, should be %d\n", __func__ , size, sizeof(struct scsi_cbw));
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    if (cbw.sig != USB_BBB_CBW_SIG) {
	    log_printf("[USB BBB] %s: CBW not valid: signature is %x, should be %x\n", __func__ , cbw.sig, USB_BBB_CBW_SIG);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }

    if (cbw.flags.reserved || cbw.lun.reserved || cbw.cdb_len.reserved || cbw.lun.lun) {
	    /* XXX: the only valid LUN for our device is 0 */
	    /* TODO: check that cbw.cdb_len and cbw.cdb are in accordance
	     * with InferfaceSubClass
             */
        log_printf("[USB BBB] %s: CBW not meaningful\n", __func__);
        errcode = MBED_ERROR_INVPARAM;
        goto err;
    }
    set_u32_with_membarrier(&bbb_ctx.tag, cbw.tag);
    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_CMD);
#ifndef __FRAMAC__
    if(handler_sanity_check_with_panic((physaddr_t)bbb_ctx.cb_cmd_received)){
        goto err;
    }
#endif
    /*@ assert bbb_ctx.cb_cmd_received \in {scsi_parse_cdb} ;*/
    /*@ calls scsi_parse_cdb ; */
    bbb_ctx.cb_cmd_received(cbw.cdb, cbw.cdb_len.cdb_len);
err:
    return errcode;
}

#ifndef __FRAMAC__
static
#endif
mbed_error_t usb_bbb_data_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep __attribute__((unused)))
{
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[USB BBB] %s (state: %x)\n", __func__, bbb_ctx.state);
    switch (bbb_ctx.state) {
        case USB_BBB_STATE_READY:
            errcode = usb_bbb_cmd_received(size);
            break;
        case USB_BBB_STATE_STATUS:
            bbb_ctx.state = USB_BBB_STATE_READY;
            break;
        case USB_BBB_STATE_DATA:
#ifndef __FRAMAC__
            if(handler_sanity_check((physaddr_t)bbb_ctx.cb_data_received)){
                goto err;
            }
#endif
            bbb_ctx.cb_data_received(size);
            break;
        default:
            log_printf("[USB BBB] %s: ERROR usb_bbb_data_received ... \n", __func__);
    }
err:
    return errcode;
}

#ifndef __FRAMAC__
static
#endif
mbed_error_t usb_bbb_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep __attribute__((unused)))
{
    log_printf("[USB BBB] %s (state: %x)\n", __func__, bbb_ctx.state);
    switch (bbb_ctx.state) {
	    case USB_BBB_STATE_STATUS:
            read_next_cmd();
            break;
        case USB_BBB_STATE_DATA:
#ifndef __FRAMAC__
            if(handler_sanity_check((physaddr_t)bbb_ctx.cb_data_sent)){
                goto err;
            }
#endif
            bbb_ctx.cb_data_sent();
            break;
        case USB_BBB_STATE_READY:
            break;
        case USB_BBB_STATE_CMD:
            break;
        default:
            log_printf("[USB BBB] %s: Unknown bbb_ctx.state\n", __func__);
    }
err:
    return MBED_ERROR_NONE;
}

void usb_bbb_declare(void (*cmd_received)(uint8_t cdb[], uint8_t cdb_len),
                     void(*data_received)(uint32_t), void(*data_sent)(void))
{
    log_printf("[USB BBB] %s\n", __func__);
    /*  sanitize */
    if (cmd_received == NULL || data_received == NULL) {
        log_printf("[BBB] invalid callbacks value\n");
        goto err;
    }
    /*XXX: add to context instead */
    bbb_ctx.cb_cmd_received = cmd_received;
    bbb_ctx.cb_data_received = data_received;
    bbb_ctx.cb_data_sent = data_sent;
    /* the following should not be requested (init phase, no async events) but
     * keeped for protection */
    request_data_membarrier();
err:
    return;
}

mbed_error_t usb_bbb_configure(uint32_t usbdci_handler)
{
    log_printf("[USB BBB] %s\n", __func__);
    mbed_error_t errcode = MBED_ERROR_NONE;

    /* these are ioep_handlers, pushed to libxDCI */
#ifndef __FRAMAC__
    ADD_LOC_HANDLER(usb_bbb_data_received)
    ADD_LOC_HANDLER(usb_bbb_data_sent)
    ADD_LOC_HANDLER(mass_storage_class_rqst_handler)
#endif

    /* here we should not require memory barrier, as we are
     * in init phase */
    bbb_ctx.iface.usb_class = USB_CLASS_MSC_UMS;
    bbb_ctx.iface.usb_subclass = 0x6; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    bbb_ctx.iface.usb_protocol = 0x50; /* Protocol BBB (Bulk only) */
    bbb_ctx.iface.dedicated = false;
    bbb_ctx.iface.rqst_handler = mass_storage_class_rqst_handler;
    bbb_ctx.iface.class_desc_handler = NULL;
    bbb_ctx.iface.usb_ep_number = 2;

    bbb_ctx.iface.eps[0].type        = USB_EP_TYPE_BULK;
    bbb_ctx.iface.eps[0].dir         = USB_EP_DIR_OUT;
    bbb_ctx.iface.eps[0].attr        = USB_EP_ATTR_NO_SYNC;
    bbb_ctx.iface.eps[0].usage       = USB_EP_USAGE_DATA;
    bbb_ctx.iface.eps[0].pkt_maxsize = 512; /* mpsize on EP1 */
    bbb_ctx.iface.eps[0].ep_num      = 1; /* this may be updated by libctrl */
    bbb_ctx.iface.eps[0].handler     = usb_bbb_data_received;

    bbb_ctx.iface.eps[1].type        = USB_EP_TYPE_BULK;
    bbb_ctx.iface.eps[1].dir         = USB_EP_DIR_IN;
    bbb_ctx.iface.eps[1].attr        = USB_EP_ATTR_NO_SYNC;
    bbb_ctx.iface.eps[1].usage       = USB_EP_USAGE_DATA;
    bbb_ctx.iface.eps[1].pkt_maxsize = 512; /* mpsize on EP2 */
    bbb_ctx.iface.eps[1].ep_num      = 2; /* this may be updated by libctrl */
    bbb_ctx.iface.eps[1].handler     = usb_bbb_data_sent;

    errcode = usbctrl_declare_interface(usbdci_handler, (usbctrl_interface_t*)&(bbb_ctx.iface));
    /* the following should not be requested (init phase, no async events) but
     * keeped for protection */
    request_data_membarrier();

    return errcode;
}

void usb_bbb_reconfigure(void)
{
    log_printf("[USB BBB] %s\n", __func__);

    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_READY);
}

/* Command Status Wrapper */
struct __packed scsi_csw {
    uint32_t sig;
    uint32_t tag;
    uint32_t data_residue;
    uint8_t status;
};

#define USB_BBB_CSW_SIG			0x53425355      /* "USBS" */

void usb_bbb_send_csw(enum csw_status status, uint32_t data_residue)
{
    log_printf("[USB BBB] %s: status %d\n", __func__, status);
    mbed_error_t errcode = MBED_ERROR_NONE;
    struct scsi_csw csw = {
        .sig = USB_BBB_CSW_SIG,
        .tag = bbb_ctx.tag,
        .data_residue = data_residue,
        .status = status
    };

    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_STATUS);
    log_printf("[USB BBB] %s: Sending CSW (%x, %x, %x, %x)\n", __func__, csw.sig,
            csw.tag, csw.data_residue, csw.status);
    errcode = usb_backend_drv_send_data((uint8_t *) & csw, sizeof(csw), bbb_ctx.iface.eps[1].ep_num);
    if (errcode != MBED_ERROR_NONE) {
        log_printf("failure while sending data: err=%d\n", errcode);
    }
}

void usb_bbb_send(const uint8_t * src, uint32_t size)
{
    log_printf("[USB BBB] %s: %dB\n", __func__, size);
    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_DATA);
    usb_backend_drv_send_data((uint8_t *)src, size, bbb_ctx.iface.eps[1].ep_num);
}

void usb_bbb_recv(void *dst, uint32_t size)
{
    log_printf("[USB BBB] %s: %dB\n", __func__, size);
    set_u8_with_membarrier(&bbb_ctx.state, USB_BBB_STATE_DATA);
    usb_backend_drv_set_recv_fifo(dst, size, bbb_ctx.iface.eps[0].ep_num);
    usb_backend_drv_activate_endpoint(bbb_ctx.iface.eps[0].ep_num, USB_BACKEND_DRV_EP_DIR_OUT);
}
