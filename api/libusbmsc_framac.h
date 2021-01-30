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
#ifndef LIBUSBMSC_FRAMAC_
#define LIBUSBMSC_FRAMAC_

#include "libc/types.h"

#ifdef __FRAMAC__
/*
 * This header is used for upper layer proof composition.
 * Some of the exported API of the libusbmsc assigns usbmsc-private global variables.
 * To make this border effect visible to the upper stack without requiring from it
 * to know exactly how libusbmsc globals are specified (types, structures and so on),
 * we use an opaque here.
 * The goal is to avoid, when compositioning multiple stacks from the driver to the
 * application, highly complex ACSL annotations due to the overall globals impact.
 * In exchange, each layer **must have all its internals border effects proven**.
 *
 * This permit to rely on the belowing stack proof and using the public specification
 * as admitted instead.
 *
 */
/*@ ghost
// When set, this means that the corresponding usbmsc API impact one of the usbmsc-local
// private global content.
uint8_t GHOST_opaque_usbmsc_privates = 1;
*/


#endif/*!__FRAMAC__*/

#endif/*!LIBUSBMSC_FRAMAC_*/
