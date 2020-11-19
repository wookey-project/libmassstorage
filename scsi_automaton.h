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
#ifndef SCSI_AUTOMATON_H_
#define SCSI_AUTOMATON_H_

#include "libc/types.h"
#include "api/scsi.h"
#include "scsi_cmd.h"

#ifndef __FRAMAC__
typedef enum scsi_state {
    SCSI_IDLE = 0x00,
    SCSI_ERROR,
} scsi_state_t;
#endif

scsi_state_t scsi_get_state(void);

void    scsi_set_state(const scsi_state_t new_state);

uint8_t scsi_next_state(scsi_state_t current_state,
                        scsi_operation_code_t request);

bool    scsi_is_valid_transition(scsi_state_t current_state,
                                 scsi_operation_code_t request);

#endif /*!SCSI_AUTOMATON_H_ */
