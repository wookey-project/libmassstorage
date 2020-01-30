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
#include "usb_bbb.h"
#include "usb_control_mass_storage.h"
#include "usbmass_desc.h"
#include "libc/syscall.h"
#include "libc/sanhandlers.h"
#include "libusbotghs.h"

static mass_storage_reset_trigger_t ms_reset_trigger = NULL;
static device_reset_trigger_t device_reset_trigger = NULL;


/*
 * Enumeration phase MS_RESET
 */
static void mass_storage_reset(void)
{
    aprintf("Bulk-Only Mass Storage Reset\n");
    if (ms_reset_trigger != NULL) {
        /* Sanity check our callback before calling it */
        if(handler_sanity_check((void*)ms_reset_trigger)){
            sys_exit();
            return;
        }
        else{
            ms_reset_trigger();
        }
    }
}

/*
 * Nominal phase device reset (critical communication error with device)
 */
static void full_device_reset(void)
{
    aprintf("Bulk-Only Mass Storage Reset\n");
    if(device_reset_trigger != NULL){
        /* Sanity check our callback before calling it */
        if(handler_sanity_check((void*)device_reset_trigger)){
            sys_exit();
            return;
        }
        else{
            device_reset_trigger();
        }
    }
}



/**
 * \brief Class request handling for bulk mode.
 *
 * @param packet Setup packet
 */
mbed_error_t mass_storage_class_rqst_handler(usbctrl_context_t *ctx __attribute__((unused)),
                                             usbctrl_setup_pkt_t *packet)
{
    uint8_t max_lun = 0;
    mbed_error_t errcode = MBED_ERROR_NONE;

    printf("[classRqst] handling MSS class rqst\n");
    switch (packet->bRequest) {
        case USB_RQST_GET_MAX_LUN:
            printf("[classRqst] handling MSS max LUN\n");
            usbotghs_send_data(&max_lun, sizeof(max_lun), EP0);
            usbotghs_endpoint_clear_nak(0, USBOTG_HS_EP_DIR_OUT);
            break;
        case USB_RQST_MS_RESET:
            printf("[classRqst] handling MSS MS RST\n");
            mass_storage_reset();       // FIXME We must use a callback function
            read_next_cmd();
            usbotghs_send_zlp(0);
            break;
        default:
            printf("Unhandled class request (%x)\n", packet->bRequest);
            usbotghs_endpoint_stall(0, USBOTG_HS_EP_DIR_IN);
            goto err;
            break;
    }
err:
    return errcode;
}

