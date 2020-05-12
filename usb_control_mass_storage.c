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
#include "usb.h"
#include "usb_bbb.h"
#include "usb_control_mass_storage.h"
#include "usbmass_desc.h"
#include "libc/syscall.h"
#include "libc/sanhandlers.h"

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
void mass_storage_class_rqst_handler(struct usb_setup_packet *packet)
{
    uint8_t max_lun = 0;

    switch (packet->bRequest) {
        case USB_RQST_GET_MAX_LUN:
#ifdef CONFIG_USR_DRV_USB_FS
            usb_driver_setup_send(&max_lun, sizeof(max_lun),
                                  USB_FS_DXEPCTL_EP0);
            usb_driver_setup_read(NULL, 0, USB_FS_DXEPCTL_EP0); //FIXME why this here ?
#endif
#ifdef CONFIG_USR_DRV_USB_HS
            usb_driver_setup_send(&max_lun, sizeof(max_lun),
                                  USB_HS_DXEPCTL_EP0);
            usb_driver_setup_read(NULL, 0, USB_HS_DXEPCTL_EP0); //FIXME why this here ?
#endif

            break;
        case USB_RQST_MS_RESET:
            mass_storage_reset();       // FIXME We must use a callback function
            read_next_cmd();
            break;
            // FIXME: break here or not????
        default:
            /* TODO: send error status */
            printf("Unhandled class request (%x)\n", packet->bRequest);
            break;
    }
}


static void mass_storage_mft_string_desc_rqst_handler(uint16_t wLength)
{
    uint32_t i;
    uint32_t len;

    printf("MFT String, wLength:\n", wLength);
    usb_string_descriptor_t string_desc;

    if (wLength == 0) {
        usb_driver_setup_send_status(0);
        usb_driver_setup_read_status();
        return;
    }

    string_desc.bDescriptorType = USB_DESC_STRING;
    len = MSFT100_SIG_SIZE + 4;
    string_desc.bLength = 0x12;
    string_desc.bDescriptorType = 0x03;
    for (i = 0; i < MSFT100_SIG_SIZE; i++)
        string_desc.wString[i] = MSFT100_SIG[i];
    string_desc.wString[MSFT100_SIG_SIZE] = 0x05;
    string_desc.wString[MSFT100_SIG_SIZE + 1] = 0x00;

    if (wLength > string_desc.bLength) {
        usb_driver_setup_send((uint8_t *) & string_desc, string_desc.bLength,
                              EP0);
    } else {
        usb_driver_setup_send((uint8_t *) & string_desc, wLength, EP0);
    }
    usb_driver_setup_read_status();
}


/**
 * \brief Set callback for class_rqst in usb_control
 */
void mass_storage_init(mass_storage_reset_trigger_t
                       upper_stack_ms_reset_trigger,
                       device_reset_trigger_t upper_stack_device_reset_trigger)
{
    /* Refister our callbacks */
    ADD_LOC_HANDLER(mass_storage_class_rqst_handler)
    ADD_LOC_HANDLER(mass_storage_mft_string_desc_rqst_handler)
    ADD_LOC_HANDLER(full_device_reset)
    usb_ctrl_callbacks_t usbmass_usb_ctrl_callbacks = {
        .class_rqst_handler = mass_storage_class_rqst_handler,
        .vendor_rqst_handler = NULL,
        .set_configuration_rqst_handler = NULL,
        .set_interface_rqst_handler = NULL,
        .functional_rqst_handler = NULL,
        .mft_string_rqst_handler = mass_storage_mft_string_desc_rqst_handler,
        .reset_handler = full_device_reset,
    };
    ms_reset_trigger = upper_stack_ms_reset_trigger;
    device_reset_trigger = upper_stack_device_reset_trigger;

    usb_ctrl_init(usbmass_usb_ctrl_callbacks, usbmass_device_desc,
                  usbmass_configuration_desc);
}
