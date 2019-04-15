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
/** @file usb_desc.h
 * \brief Contains usb mass storage descriptors
 */
#ifndef _USBMASS_DESC_H
#define _USBMASS_DESC_H

#include "autoconf.h"
#include "usb_control.h"
//#include "usb_device.h"

#define USB_NB_INTERFACE        1


/* Classes, subclasses and protocols for DFU Runtime */
#define USB_CLASS_MASS_STORAGE    0x08
#define USB_SUBCLASS_SCSI         0x06
#define USB_PROTOCOL_BBB          0x50 /* Bulk only */


/* Microsoft Vendor Code used for OS Descriptor request */
static uint8_t MSFT100_SIG[MSFT100_SIG_SIZE] = {
            0x4D, 0x00, 0x53, 0x00, 0x46, 0x00, 0x54, 0x00,
            0x31, 0x00, 0x30, 0x00, 0x30, 0x00
};


/**
 * \brief Device descriptor
 *
 * The device descriptor of a USB device represents the entire device.
 * An USB device can only have one device descriptor. It specifies information about the device such as:
 *    - the supported USB version,
 *    - maximum packet size,
 *    - vendor and product IDs and the number of possible configurations the device can have.
 * The format of the device descriptor is defined below.
 */
const usb_ctrl_device_descriptor_t usbmass_device_desc = {
	.bLength = 18,
	.bDescriptorType = USB_DESC_DEVICE,
	.bcdUSB = 0x0200,       /* USB 2.0 */
	.bDeviceClass = 0,
	.bDeviceSubClass = 0,
	.bDeviceProtocol = 0,
	.bMaxPacketSize = 64,
	.idVendor = CONFIG_USB_DEV_VENDORID,
	.idProduct = CONFIG_USB_DEV_PRODUCTID,
	.bcdDevice = 0x000,
	.iManufacturer = CONFIG_USB_DEV_MANUFACTURER_INDEX,
	.iProduct = CONFIG_USB_DEV_PRODNAME_INDEX,
	.iSerialNumber = CONFIG_USB_DEV_SERIAL_INDEX,
	.bNumConfigurations = 1, /* We only have 1 interface for the DFU app */
};

/**
 * \brief Configuration descriptor
 *
 */
const usb_ctrl_full_configuration_descriptor_t usbmass_configuration_desc = {
	.config_desc = {
    	.bLength = sizeof(usb_ctrl_configuration_descriptor_t),
    	.bDescriptorType = USB_DESC_CONFIG,
    	.wTotalLength = sizeof(usb_ctrl_full_configuration_descriptor_t),
        .bNumInterfaces = USB_NB_INTERFACE,
    	.bConfigurationValue = 1,
    	.iConfiguration = 0,
    	.bmAttributes.reserved7 = 1,
    	.bmAttributes.self_powered = 1,
    	.bmAttributes.remote_wakeup = 0,
    	.bmAttributes.reserved = 0,
    	.bMaxPower = 0,
    },
	.interface_desc = {
    	.bLength = sizeof(usb_ctrl_interface_descriptor_t),
    	.bDescriptorType = USB_DESC_INTERFACE,
    	.bInterfaceNumber = 0,
    	.bAlternateSetting = 0,
    	.bNumEndpoints = 2,
    	.bInterfaceClass = USB_CLASS_MASS_STORAGE,
    	.bInterfaceSubClass = USB_SUBCLASS_SCSI,
    	.bInterfaceProtocol = USB_PROTOCOL_BBB,
    	.iInterface = 1,
    },
    .ep = {
	.ep_in = {
        .bLength = sizeof(usb_ctrl_endpoint_descriptor_t),
        .bDescriptorType = USB_DESC_EP,
        .bEndpointAddress = 0x82,
        .bmAttributes = (USB_EP_TYPE_BULK | USB_EP_ATTR_NO_SYNC | USB_EP_USAGE_DATA),
        .wMaxPacketSize = MAX_DATA_PACKET_SIZE(2),
        .bInterval = 0x00,
        },
	.ep_out = {
        .bLength = sizeof(usb_ctrl_endpoint_descriptor_t),
        .bDescriptorType = USB_DESC_EP,
        .bEndpointAddress = 0x1,
        .bmAttributes = (USB_EP_TYPE_BULK | USB_EP_ATTR_NO_SYNC | USB_EP_USAGE_DATA),
        .wMaxPacketSize = MAX_DATA_PACKET_SIZE(1),
        .bInterval = 0x00,
        },
    },
};


usb_ctrl_callbacks_t cb = {
    .class_rqst_handler  = mass_storage_class_rqst_handler,
    .vendor_rqst_handler = NULL,
    .set_configuration_rqst_handler = NULL,
    .set_interface_rqst_handler = NULL,
    .functional_rqst_handler = NULL,

};

#endif /* !_USBMASS_DESC_H */


