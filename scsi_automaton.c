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
#include "scsi_automaton.h"
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/string.h"


/****************************************************************
 * SCSI state automaton formal definition and associate utility
 * functions
 ***************************************************************/

static scsi_state_t state;

/*
 * all allowed transitions and target states for each current state
 * empty fields are set as 0xff/0xff for request/state couple, which is
 * an inexistent state and request
 *
 * This table associate each state of the DFU automaton with up to
 * 5 potential allowed transitions/next_state couples. This permit to
 * easily detect:
 *    1) authorized transitions, based on the current state
 *    2) next state, based on the current state and current transition
 *
 * If the next_state for the current transision is keeped to 0xff, this
 * means that the current transition for the current state may lead to
 * multiple next state depending on other informations. In this case,
 * the transition handler has to handle this manually.
 */

# define MAX_TRANSITION_STATE 17

/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */
typedef struct scsi_operation_code_transition {
    uint8_t    request;
    uint8_t    target_state;
} scsi_operation_code_transition_t;


static const struct {
    scsi_state_t          state;
    scsi_operation_code_transition_t  req_trans[MAX_TRANSITION_STATE];
} scsi_automaton[] = {
    { SCSI_IDLE,               {
                                {SCSI_CMD_INQUIRY,SCSI_IDLE},
                                {SCSI_CMD_MODE_SELECT_10,SCSI_IDLE},
                                {SCSI_CMD_MODE_SELECT_6,SCSI_IDLE},
                                {SCSI_CMD_MODE_SENSE_10,SCSI_IDLE},
                                {SCSI_CMD_MODE_SENSE_6,SCSI_IDLE},
                                {SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL,SCSI_IDLE},
                                {SCSI_CMD_READ_6,SCSI_IDLE},
                                {SCSI_CMD_READ_10,SCSI_IDLE},
                                {SCSI_CMD_READ_CAPACITY_10,SCSI_IDLE},
                                {SCSI_CMD_READ_CAPACITY_16,SCSI_IDLE},
                                {SCSI_CMD_READ_FORMAT_CAPACITIES,SCSI_IDLE},
                                {SCSI_CMD_REPORT_LUNS,SCSI_IDLE},
                                {SCSI_CMD_REQUEST_SENSE,SCSI_IDLE},
                                {SCSI_CMD_SEND_DIAGNOSTIC,SCSI_IDLE},
                                {SCSI_CMD_TEST_UNIT_READY,SCSI_IDLE},
                                {SCSI_CMD_WRITE_6,SCSI_IDLE},
                                {SCSI_CMD_WRITE_10,SCSI_IDLE},
                             }
    },
    { SCSI_READ,     {
                                 {SCSI_CMD_READ_6,SCSI_IDLE},
                                 {SCSI_CMD_READ_10,SCSI_IDLE},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},


                             }
    },
    { SCSI_WRITE,     {
                                 {SCSI_CMD_WRITE_6,SCSI_IDLE},
                                 {SCSI_CMD_WRITE_10,SCSI_IDLE},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                             }
    },
    { SCSI_ERROR,     {
                                 {SCSI_CMD_MODE_SENSE_10, SCSI_IDLE},
                                 {SCSI_CMD_MODE_SENSE_6, SCSI_IDLE},
                                 {SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL,SCSI_IDLE},
                                 {SCSI_CMD_REQUEST_SENSE,SCSI_IDLE},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                                 {0xff,0xff},
                             },
    },

};

/**********************************************
 * SCSI getters and setters
 *********************************************/

scsi_state_t scsi_get_state(void)
{
    return state;
}


/*
 * This function is eligible in both main thread and ISR
 * mode (through trigger execution). Please use aprintf only
 * here.
 */
void scsi_set_state(const scsi_state_t new_state)
{
    if (new_state == 0xff) {
        aprintf("%s: PANIC! this should never arise !", __func__);
        while (1) {}; //FIXME
        return;
    }
#if SCSI_DEBUG
    aprintf("%s: state: %x => %x\n", __func__, scsi_ctx.state, new_state);
#endif
    state = new_state;
}

/******************************************************
 * SCSI automaton management function (transition and
 * state check)
 *****************************************************/

/*!
 * \brief return the next automaton state
 *
 * The next state is returned depending on the current state
 * and the current request. In some case, it can be 0xff if multiple
 * next states are possible.
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return the next state, or 0xff
 */
uint8_t scsi_next_state(scsi_state_t  current_state, scsi_operation_code_t    request)
{
    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (scsi_automaton[current_state].req_trans[i].request == request) {
            return (scsi_automaton[current_state].req_trans[i].target_state);
        }
    }
    /* fallback, no corresponding request found for  this state */
    return 0xff;
}

/*!
 * \brief Specify if the current request is valid for the current state
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return true if the transition request is allowed for this state, or false
 */
bool scsi_is_valid_transition(scsi_state_t             current_state,
                              scsi_operation_code_t    request)
{
    for (uint8_t i = 0; i < MAX_TRANSITION_STATE; ++i) {
        if (scsi_automaton[current_state].req_trans[i].request == request) {
            return true;
        }
    }
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should stall the request.
     */
    printf("%s: invalid transition from state %d, request %d\n", __func__, current_state, request);
    scsi_set_state(SCSI_ERROR);
    return false;
}


