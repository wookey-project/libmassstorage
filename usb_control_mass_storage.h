/** @file usb_control_mass_storage.h
 *
 */
#ifndef _USB_CONTROL_MASS_STORAGE_H
#define _USB_CONTROL_MASS_STORAGE_H

#include "usb_control.h"

void mass_storage_class_rqst_handler(struct usb_setup_packet *packet);

void mass_storage_init(void);

#endif /* _USB_CONTROL_MASS_STORAGE_H */
