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
/** @file usb_control_mass_storage.c
 *
 */
#include "autoconf.h"
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/regutils.h"

#ifdef __FRAMAC__
# include "usbmsc_framac_private.h"
#endif


#include "scsi_dbg.h"
#include "usb_bbb.h"
#include "usb_control_mass_storage.h"
#include "usbmass_desc.h"
#include "libc/syscall.h"
#include "libc/sanhandlers.h"
#include "libusbctrl.h"
#include "api/libusbmsc.h"

static mass_storage_reset_trigger_t ms_reset_trigger = usbmsc_reset_stack;

/*
 * Enumeration phase MS_RESET
 */
/*@
  @ assigns \nothing;
  */
#ifndef __FRAMAC__
static
#endif
void mass_storage_reset(void)
{
    log_printf("Bulk-Only Mass Storage Reset\n");
    if (ms_reset_trigger != NULL) {
        /* Sanity check our callback before calling it */
#ifndef __FRAMAC__
        /* INFO: ms_reset_trigger is an upper layer callaback. Here, we consider upper
         * layer content as assigning nothing, as the current proof is handling local library
         * proof, not upper one. */
        if (handler_sanity_check((physaddr_t)ms_reset_trigger)) {
            return;
        } else {
            ms_reset_trigger();
        }
#endif
    }
}

/*
 * Nominal phase device reset (critical communication error with device)
 */

/**
 * \brief Class request handling for bulk mode.
 *
 * @param packet Setup packet
 */
/*@
    @ requires \separated(packet,&GHOST_opaque_drv_privates, &bbb_ctx, &scsi_ctx, &GHOST_in_eps[bbb_ctx.iface.eps[1].ep_num]);
    @ assigns GHOST_in_eps[0].state, GHOST_opaque_drv_privates,
           bbb_ctx.state, bbb_ctx.state;
  */
mbed_error_t mass_storage_class_rqst_handler(uint32_t usbdci_handler __attribute__((unused)),
                                             usbctrl_setup_pkt_t *packet)
{
    uint8_t max_lun = 0;
    mbed_error_t errcode = MBED_ERROR_NONE;

    log_printf("[classRqst] handling MSS class rqst\n");
    switch (packet->bRequest) {
        case USB_RQST_GET_MAX_LUN:
            log_printf("[classRqst] handling MSS max LUN\n");
            usb_backend_drv_send_data(&max_lun, sizeof(max_lun), EP0);
            usb_backend_drv_ack(0, USB_BACKEND_DRV_EP_DIR_OUT);
            break;
        case USB_RQST_MS_RESET:
            log_printf("[classRqst] handling MSS MS RST\n");
            mass_storage_reset();       // FIXME We must use a callback function
            read_next_cmd();
            usb_backend_drv_send_zlp(0);
            break;
        default:
            log_printf("Unhandled class request (%x), not for me\n", packet->bRequest);
            errcode = MBED_ERROR_INVPARAM;
            goto err;
            break;
    }
err:
    return errcode;
}

