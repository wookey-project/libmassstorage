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
/** @file usb_control_mass_storage.h
 *
 */
#ifndef _USB_CONTROL_MASS_STORAGE_H
#define _USB_CONTROL_MASS_STORAGE_H

typedef void (*mass_storage_reset_trigger_t)(void);
typedef void (*device_reset_trigger_t)(void);

mbed_error_t mass_storage_class_rqst_handler(uint32_t usbdci_handler __attribute__((unused)),
                                             usbctrl_setup_pkt_t *packet);

void    mass_storage_init(mass_storage_reset_trigger_t
                          upper_stack_ms_reset_trigger,
                          device_reset_trigger_t
                          upper_stack_device_reset_trigger);

#endif /* _USB_CONTROL_MASS_STORAGE_H */
