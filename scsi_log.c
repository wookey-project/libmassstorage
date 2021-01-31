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
#ifdef __FRAMAC__
/* static inline functions generate function shadowing which make analysis harder with FramaC.
 * For analysis purpose, we replace the static inline function by the exact same content, but without
 * static inline
 */

#include "scsi_log.h"

/* SCSI errors */
/*@
  @ assigns \nothing;
  */
scsi_sense_key_t scsi_error_get_sense_key(uint32_t error)
{
    return (scsi_sense_key_t) ((error & 0xf0000) >> 16);
}

/*@
  @ assigns \nothing;
  */
uint8_t scsi_error_get_asc(uint32_t error)
{
    return (uint8_t) ((error & 0xff00) >> 8);
}

/*@
  @ assigns \nothing;
  */
uint8_t scsi_error_get_ascq(uint32_t error)
{
    return (uint8_t) (error & 0xff);
}


#endif/*!__FRAMAC__*/
