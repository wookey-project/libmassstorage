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
#include "libc/syscall.h"
#include "libc/sanhandlers.h"
#include "usb_control_mass_storage.h"


#define BBB_DEBUG 0

enum bbb_state {
    READY,
    CMD,
    DATA,
    STATUS,
};

static void (*callback_cmd_received)(uint8_t cdb[], uint8_t cdb_len);
static void (*callback_data_received)(uint32_t size);
static void (*callback_data_sent)(void);


volatile enum bbb_state bbb_state;
uint32_t current_tag;



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
static struct scsi_cbw cbw;

#define USB_BBB_CBW_SIG		0x43425355      /* "USBC" */

void read_next_cmd(void)
{
#if BBB_DEBUG
    printf("[USB BBB] %s: Reading a command\n", __func__);
#endif
    bbb_state = READY;
    usbotghs_set_recv_fifo((uint8_t*)&cbw, sizeof(cbw), 1);
    usbotghs_activate_endpoint(1, USBOTG_HS_EP_DIR_OUT);
}

extern volatile bool reset_requested;

static void usb_bbb_cmd_received(uint32_t size)
{
#if 0
    if(reset_requested == true){
        while(reset_requested == true) {
	    continue;
        }
        return;
    }
#endif

    if (size != sizeof(struct scsi_cbw)) {
	    printf("[USB BBB] %s: CBW not valid, size %d, should be %d\n", __func__ , size, sizeof(struct scsi_cbw));
            return;
    }
    if (cbw.sig != USB_BBB_CBW_SIG) {
	    printf("[USB BBB] %s: CBW not valid: signature is %x, should be %x\n", __func__ , cbw.sig, USB_BBB_CBW_SIG);
            return;
    }

    if (cbw.flags.reserved || cbw.lun.reserved || cbw.cdb_len.reserved || cbw.lun.lun) {
	    /* XXX: the only valid LUN for our device is 0 */
	    /* TODO: check that cbw.cdb_len and cbw.cdb are in accordance
	     * with InferfaceSubClass
             */
#if BBB_DEBUG
        printf("[USB BBB] %s: CBW not meaningful\n", __func__);
#endif
        return;
    }
    current_tag = cbw.tag;
    bbb_state = CMD;
#if BBB_DEBUG
    printf("[USB BBB] %s: Command received\n", __func__);
#endif
    /* Sanity check our callback before calling it */
    if(handler_sanity_check((void*)callback_cmd_received)){
        sys_exit();
        return;
    }
    else{
        callback_cmd_received(cbw.cdb, cbw.cdb_len.cdb_len);
    }
}

static mbed_error_t usb_bbb_data_received(uint32_t dev_id __attribute__((unused)), uint32_t size, uint8_t ep __attribute__((unused)))
{
#if 0
        if(reset_requested == true){
                while(reset_requested == true){
                        continue;
                }
                return;
        }
#endif

#if BBB_DEBUG
    printf("[USB BBB] %s bbb_state: %x ... \n", __func__, bbb_state);
#endif
    switch (bbb_state) {
        case READY:
            usb_bbb_cmd_received(size);
            break;
        case STATUS:
            bbb_state = READY;
            break;
        case DATA:
            /* Sanity check our callback before calling it */
            if(handler_sanity_check((void*)callback_data_received)){
               sys_exit();
               return;
            }
            else{
                callback_data_received(size);
            }
            break;
        default:
            printf("[USB BBB] %s: ERROR usb_bbb_data_received ... \n",
                    __func__);
    }
    return MBED_ERROR_NONE;
}

static mbed_error_t usb_bbb_data_sent(uint32_t dev_id __attribute__((unused)), uint32_t size __attribute__((unused)), uint8_t ep __attribute__((unused)))
{
#if 0
    if(reset_requested == true){
        while(reset_requested == true){
            continue;
	}
	return;
    }
#endif

    switch (bbb_state) {
	    case STATUS:
#if BBB_DEBUG
            printf("[USB BBB] %s: data sent while in STATUS state\n",
                    __func__);
#endif
            read_next_cmd();
            break;
        case DATA:
#if BBB_DEBUG
            printf("[USB BBB] %s: data sent while in DATA state\n", __func__);
#endif
	    /* Sanity check our callback before calling it */
            if(handler_sanity_check((void*)callback_data_sent)){
                sys_exit();
                return;
            }
            else{
                callback_data_sent();
            }
            break;
        case READY:
#if BBB_DEBUG
            printf("[USB BBB] %s: data sent while in READY state\n", __func__);
#endif
            break;
        case CMD:
#if BBB_DEBUG
            printf("[USB BBB] %s: data sent while in CMD state\n", __func__);
#endif
            break;
        default:
            printf("[USB BBB] %s: Unknown bbb_state\n", __func__);
    }
    return MBED_ERROR_NONE;
}

void usb_bbb_early_init(void (*cmd_received)(uint8_t cdb[], uint8_t cdb_len),
                        void(*data_received)(uint32_t), void(*data_sent)(void))
{
#if BBB_DEBUG
    printf("[USB BBB] %s\n", __func__);
#endif
    callback_cmd_received = cmd_received;
    callback_data_received = data_received;
    callback_data_sent = data_sent;

    // XXX: usb_driver_early_init(usb_bbb_data_received, usb_bbb_data_sent);
}

void usb_bbb_init(usbctrl_context_t *ctx)
{
    /* these are ioep_handlers, pushed to libxDCI */
    ADD_LOC_HANDLER(usb_bbb_data_received)
    ADD_LOC_HANDLER(usb_bbb_data_sent)
    ADD_LOC_HANDLER(mass_storage_class_rqst_handler)

    usbctrl_interface_t iface = { 0 };
    iface.usb_class = USB_CLASS_MSC_UMS;
    iface.usb_subclass = 0x6; /* SCSI transparent cmd set (i.e. use INQUIRY) */
    iface.usb_protocol = 0x50; /* Protocol BBB (Bulk only) */
    iface.dedicated = false;
    iface.rqst_handler = mass_storage_class_rqst_handler;
    iface.class_desc_handler = NULL;
    iface.usb_ep_number = 2;

    iface.eps[0].type        = USB_EP_TYPE_BULK;
    iface.eps[0].dir         = USB_EP_DIR_OUT;
    iface.eps[0].attr        = USB_EP_ATTR_NO_SYNC;
    iface.eps[0].usage       = USB_EP_USAGE_DATA;
    iface.eps[0].pkt_maxsize = 512; /* mpsize on EP1 */
    iface.eps[0].ep_num      = 1; /* this may be updated by libctrl */
    iface.eps[0].handler     = usb_bbb_data_received;

    iface.eps[1].type        = USB_EP_TYPE_BULK;
    iface.eps[1].dir         = USB_EP_DIR_IN;
    iface.eps[1].attr        = USB_EP_ATTR_NO_SYNC;
    iface.eps[1].usage       = USB_EP_USAGE_DATA;
    iface.eps[1].pkt_maxsize = 512; /* mpsize on EP2 */
    iface.eps[1].ep_num      = 2; /* this may be updated by libctrl */
    iface.eps[1].handler     = usb_bbb_data_sent;


    usbctrl_declare_interface(ctx, &iface);
}

void usb_bbb_reinit(void)
{
    bbb_state = READY;
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
    mbed_error_t errcode = MBED_ERROR_NONE;
    struct scsi_csw csw = {
        .sig = USB_BBB_CSW_SIG,
        .tag = current_tag,
        .data_residue = data_residue,
        .status = status
    };

    bbb_state = STATUS;
#if BBB_DEBUG
    aprintf("[USB BBB] %s: Sending CSW (%x, %x, %x, %x)\n", __func__, csw.sig,
            csw.tag, csw.data_residue, csw.status);
#endif
    errcode = usbotghs_send_data((uint8_t *) & csw, sizeof(csw), 2);
    if (errcode != MBED_ERROR_NONE) {
        printf("failure while sending data: err=%d\n", errcode);
    }
}

void usb_bbb_send(const uint8_t * src, uint32_t size, uint8_t ep)
{
#if BBB_DEBUG
    aprintf("[USB BBB] %s\n", __func__);
#endif
    bbb_state = DATA;
    usbotghs_send_data((uint8_t *)src, size, ep);
}

void usb_bbb_read(void *dst, uint32_t size, uint8_t ep)
{
    ep = ep;
#if BBB_DEBUG
    aprintf("[USB BBB] %s\n", __func__);
#endif
    bbb_state = DATA;
    usbotghs_set_recv_fifo(dst, size, 1);
    usbotghs_activate_endpoint(1, USBOTG_HS_EP_DIR_OUT);
}
