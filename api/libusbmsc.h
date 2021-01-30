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
#ifndef LIBUSBMSC_H
# define LIBUSBMSC_H

#include "libusbctrl.h"

/*********************************************************************************
 * About Frama-C header
 * When using Frama-C, some static globals may need to be moved here instead of in
 * local C or header files in order to define properly function contacts.
 * There is no variables or type collisioning, and the behavior of the programs is the
 * same.
 */

#ifdef __FRAMAC__
# include "libusbmsc_framac.h"
#endif



/**
 * SCSI stack implementation
 */

/*****************************************************
 * externally supplied implementations prototypes
 *
 * WARNING: these functions MUST be defined in the binary
 * which include the libSCSI. These functions implement
 * the backend storage access, which may vary depending on
 * the overall system implementation and which is not, as a
 * consequence, a SCSI specific implementation.
 *****************************************************/

/*
 * Why using symbol resolution instead of callbacks ?
 *
 * Symbol resolution is made at link time, instead of requiring
 * function pointers that need to be registered in a writable
 * area of the application memory.
 *
 * A lot of security vulnerabilities are based on function pointers
 * corruption using overflows on stack contexts, making ROP or
 * any other uncontrolled execution flows possible.
 *
 * Moreover, linking directly to the symbol avoid a resolution of
 * the callback address and help the compiler at optimization time.
 */


/*
 * \brief Read data from the storage backend
 *
 * \param sector_addr SCSI sector address where the data must be read
 * \param num_sectors number of sectors to read
 *
 * \return 0 on success
 */
mbed_error_t usbmsc_storage_backend_read(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief Write data to the storage backend
 *
 * \param sector_addr SCSI sector address where the data must be written
 * \param num_sectors number of sectors to write
 *
 * \return 0 on success
 */
mbed_error_t usbmsc_storage_backend_write(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief get back the backend storage capacity
 *
 * \param numblock number of SCSI blocks
 * \param blocksize size of one SCSI block
 *
 * \return 0 on success
 */
mbed_error_t usbmsc_storage_backend_capacity(uint32_t *numblocks, uint32_t *blocksize);


/*
 * \brief respond to a reset has been received on the line
 *
 * When a reset has been received on control endpoint while the SCSI state
 * machine is running, this means that something bad happened. The policy to
 * handle this reset softly, or hardly (for e.g. by rebooting) is leaving
 * to the user task, depending on the global device software stack.
 *
 * This function is triggered only *after* the enumeration phase, until the
 * SCSI stack is up and running.
 *
 */
void usbmsc_reset_stack(void);

/***********************************************************
 * libSCSI API
 ***********************************************************/

mbed_error_t usbmsc_declare(uint8_t * buf, uint16_t len);

mbed_error_t usbmsc_initialize(uint32_t usbdci_handler);

mbed_error_t usbmsc_initialize_automaton(void);

void usbmsc_reinit(void);

mbed_error_t usbmsc_exec_automaton(void);

#endif /* LIBUSBMSC_H */
