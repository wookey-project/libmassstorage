#ifndef SCSI_AUTOMATON_H_
#define SCSI_AUTOMATON_H_

#include "api/types.h"
#include "scsi_cmd.h"

typedef enum scsi_state {
    SCSI_IDLE = 0x00,
    SCSI_READ,
    SCSI_WRITE,
    SCSI_ERROR,
} scsi_state_t;

scsi_state_t scsi_get_state(void);

void         scsi_set_state(const scsi_state_t new_state);

uint8_t      scsi_next_state(scsi_state_t          current_state,
                             scsi_operation_code_t request);

bool         scsi_is_valid_transition(scsi_state_t          current_state,
                                      scsi_operation_code_t request);

#endif/*!SCSI_AUTOMATON_H_*/
