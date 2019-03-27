/** @file usb_control_mass_storage.h
 *
 */
#ifndef _USB_CONTROL_MASS_STORAGE_H
#define _USB_CONTROL_MASS_STORAGE_H

#include "usb_control.h"

typedef void (*mass_storage_reset_trigger_t)(void);

void mass_storage_class_rqst_handler(struct usb_setup_packet *packet);

void mass_storage_init(mass_storage_reset_trigger_t reset_trigger);

#endif /* _USB_CONTROL_MASS_STORAGE_H */
