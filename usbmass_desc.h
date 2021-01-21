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
//#include "usb_device.h"

#define USB_NB_INTERFACE        1


/* Classes, subclasses and protocols for DFU Runtime */
#define USB_CLASS_MASS_STORAGE    0x08
#define USB_SUBCLASS_SCSI         0x06
#define USB_PROTOCOL_BBB          0x50  /* Bulk only */

/* mass storage class USB RQST */
#define USB_RQST_GET_MAX_LUN		0xfe
#define USB_RQST_MS_RESET		    0xff

#endif /* !_USBMASS_DESC_H */
