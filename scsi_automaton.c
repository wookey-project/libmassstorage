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
#include "libc/stdio.h"
#include "libc/nostd.h"
#include "libc/string.h"
#include "libc/sync.h"
#include "scsi.h"
#include "scsi_dbg.h"


/****************************************************************
 * SCSI state automaton formal definition and associate utility
 * functions
 ***************************************************************/

//#ifndef __FRAMAC__
/* in FramaC case, state must be handled in ACSL content in usb_bbb.c, and as a
 * consequence must be exported. */
scsi_state_t state = SCSI_IDLE;

//#endif
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

#define MAX_TRANSITION_STATE 17

/* considering SCSI_ERROR the last state, states starting with 0 */
#define SCSI_NUM_STATES SCSI_ERROR + 1

/*
 * Association between a request and a transition to a next state. This couple
 * depend on the current state and is use in the following structure
 */
typedef struct scsi_operation_code_transition {
    uint8_t request;
    uint8_t target_state;
} scsi_operation_code_transition_t;


typedef struct {
    uint8_t number;
    scsi_operation_code_transition_t const *transitions;
} scsi_state_transitions_t;

/* IDLE SCSI transitions */
static const scsi_operation_code_transition_t scsi_idle_trans[17] = {
    {SCSI_CMD_INQUIRY, SCSI_IDLE},
    {SCSI_CMD_MODE_SELECT_10, SCSI_IDLE},
    {SCSI_CMD_MODE_SELECT_6, SCSI_IDLE},
    {SCSI_CMD_MODE_SENSE_10, SCSI_IDLE},
    {SCSI_CMD_MODE_SENSE_6, SCSI_IDLE},
    {SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL, SCSI_IDLE},
    {SCSI_CMD_READ_6, SCSI_IDLE},
    {SCSI_CMD_READ_10, SCSI_IDLE},
    {SCSI_CMD_READ_CAPACITY_10, SCSI_IDLE},
    {SCSI_CMD_READ_CAPACITY_16, SCSI_IDLE},
    {SCSI_CMD_READ_FORMAT_CAPACITIES, SCSI_IDLE},
    {SCSI_CMD_REPORT_LUNS, SCSI_IDLE},
    {SCSI_CMD_REQUEST_SENSE, SCSI_IDLE},
    {SCSI_CMD_SEND_DIAGNOSTIC, SCSI_IDLE},
    {SCSI_CMD_TEST_UNIT_READY, SCSI_IDLE},
    {SCSI_CMD_WRITE_6, SCSI_IDLE},
    {SCSI_CMD_WRITE_10, SCSI_IDLE}
};

/* ERROR SCSI transitions */
static const scsi_operation_code_transition_t scsi_error_trans[4] = {
    {SCSI_CMD_MODE_SENSE_10, SCSI_IDLE},
    {SCSI_CMD_MODE_SENSE_6, SCSI_IDLE},
    {SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL, SCSI_IDLE},
    {SCSI_CMD_REQUEST_SENSE, SCSI_IDLE}
};


typedef struct {
    scsi_state_t state;
    scsi_state_transitions_t trans_list;
} scsi_automaton_t;

static const scsi_automaton_t scsi_automaton[2] = {
    {
        .state = SCSI_IDLE,
        .trans_list = {
            .number = 17,
            .transitions = &scsi_idle_trans[0]
        }
    },
    {
        .state = SCSI_ERROR,
        .trans_list = {
            .number = 4,
            .transitions = &scsi_error_trans[0]
        }
    }
};

/**********************************************
 * SCSI getters and setters
 *********************************************/

/*@
  @ assigns \nothing;
  @ ensures \result == scsi_ctx.state;
   */
scsi_state_t scsi_get_state(void)
{
    scsi_context_t *ctx = scsi_get_context();
    return ctx->state;
}


/*
 * This function is eligible in both main thread and ISR
 * mode (through trigger execution). Please use aprintf only
 * here.
 */
/*@
  @ assigns scsi_ctx.state;

  @behavior invstate:
  @  assumes new_state > SCSI_ERROR;
  @  ensures scsi_ctx.state == SCSI_ERROR;

  @behavior setstate:
  @  assumes new_state <= SCSI_ERROR;
  @  ensures scsi_ctx.state == new_state;
  @  ensures SCSI_IDLE <= scsi_ctx.state <= SCSI_ERROR ;

  @ disjoint behaviors;
  @ complete behaviors;
   */
void scsi_set_state(const scsi_state_t new_state)
{
    scsi_context_t *ctx = scsi_get_context();
    if (new_state > SCSI_ERROR) {
        /*@ assert \false; */
        log_printf("%s: PANIC! this should never arise !", __func__);
        set_u8_with_membarrier(&ctx->state, SCSI_ERROR);
        goto err;
    }
    /*@ assert SCSI_IDLE <= new_state <= SCSI_ERROR ; */
    log_printf("%s: state: %x => %x\n", __func__, ctx->state, new_state);
    set_u8_with_membarrier(&ctx->state, new_state);
    /*@ assert scsi_ctx.state == new_state; */
err:
    return;
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
/*@
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;

  @ requires \separated(scsi_automaton + (0 .. 1), scsi_automaton[0].trans_list.transitions + (0 .. scsi_automaton[0].trans_list.number-1),&scsi_ctx,scsi_automaton[1].trans_list.transitions + (0 .. scsi_automaton[1].trans_list.number-1));
  @ requires \valid_read(scsi_automaton[0].trans_list.transitions + (0 .. scsi_automaton[0].trans_list.number-1));
  @ requires \valid_read(scsi_automaton[1].trans_list.transitions + (0 .. scsi_automaton[1].trans_list.number-1));
  @ assigns \nothing;

  @behavior inv_req:
  @   assumes request == 0xff;
  @   ensures \result == 0xff;

  @behavior req_found:
  @   assumes request != 0xff;
  @   assumes \exists integer i ; 0 <= i < scsi_automaton[current_state].trans_list.number && scsi_automaton[current_state].trans_list.transitions[i].request == request;
  @   ensures \result != 0xff;

  @behavior req_not_found:
  @   assumes request != 0xff;
  @   assumes \forall integer i ; 0 <= i < scsi_automaton[current_state].trans_list.number ==> scsi_automaton[current_state].trans_list.transitions[i].request != request;
  @   ensures \result == 0xff;


  @ disjoint behaviors;
  @ complete behaviors;
   */
uint8_t scsi_next_state(const scsi_state_t current_state,
                        const scsi_operation_code_t request)
{
    uint8_t result = 0xff;

    if (request == 0xff) {
        /* invalid request, may lead to invalid req_trans read */
        return result;
    }
    const uint8_t num_trans = scsi_automaton[current_state].trans_list.number;
    /*@
      @ loop invariant 0 <= i <= num_trans;
      @ loop invariant \forall integer prei; 0 <= prei < i ==> scsi_automaton[current_state].trans_list.transitions[prei].request != request;
      @ loop assigns i;
      @ loop variant num_trans - i;
      */
    for (uint8_t i = 0; i < num_trans; ++i) {
        if (scsi_automaton[current_state].trans_list.transitions[i].request == request) {
            result = scsi_automaton[current_state].trans_list.transitions[i].target_state;
            goto err;
        }
    }
    /*@ assert result == 0xff; */

err:
    return result;
}

/*!
 * \brief Specify if the current request is valid for the current state
 *
 * \param current_state the current automaton state
 * \param request       the current transition request
 *
 * \return true if the transition request is allowed for this state, or false
 */

/*@
  @ requires SCSI_IDLE <= current_state <= SCSI_ERROR;
  @ requires \separated(scsi_automaton + (0 .. 1), scsi_automaton[0].trans_list.transitions + (0 .. scsi_automaton[0].trans_list.number-1),&scsi_ctx,scsi_automaton[1].trans_list.transitions + (0 .. scsi_automaton[1].trans_list.number-1));
  @ requires \valid_read(scsi_automaton[0].trans_list.transitions + (0 .. scsi_automaton[0].trans_list.number-1));
  @ requires \valid_read(scsi_automaton[1].trans_list.transitions + (0 .. scsi_automaton[1].trans_list.number-1));
  @ assigns scsi_ctx.state;

  @ behavior inv_req:
  @   assumes request == 0xff;
  @   ensures \result == \false;
  @   ensures scsi_ctx.state == \old(scsi_ctx.state);

  @ behavior trans_valid:
  @   assumes request != 0xff;
  @   assumes current_state == SCSI_IDLE ==> \exists integer i ; 0 <= i < scsi_automaton[SCSI_IDLE].trans_list.number && scsi_automaton[SCSI_IDLE].trans_list.transitions[i].request == request;
  @   assumes current_state == SCSI_ERROR ==> \exists integer i ; 0 <= i < scsi_automaton[SCSI_ERROR].trans_list.number && scsi_automaton[SCSI_ERROR].trans_list.transitions[i].request == request;
  @   ensures \result == \true;
  @   ensures scsi_ctx.state == \old(scsi_ctx.state);

  @ behavior trans_invalid:
  @   assumes request != 0xff;
  @   assumes current_state == SCSI_IDLE ==> (\forall integer i ; 0 <= i <scsi_automaton[SCSI_IDLE].trans_list.number ==> scsi_automaton[SCSI_IDLE].trans_list.transitions[i].request != request);
  @   assumes current_state == SCSI_ERROR ==> (\forall integer i ; 0 <= i <scsi_automaton[SCSI_ERROR].trans_list.number ==> scsi_automaton[SCSI_ERROR].trans_list.transitions[i].request != request);
  @   ensures \result == \false;
  @   ensures scsi_ctx.state == SCSI_ERROR;

  @ disjoint behaviors;
  @ complete behaviors;
   */
bool scsi_is_valid_transition(const scsi_state_t current_state,
                              const scsi_operation_code_t request)
{
    bool result = false;

    if (request == 0xff) {
        /* invalid request, may lead to invalid req_trans read */
        return result;
    }


    const uint8_t num_trans = scsi_automaton[current_state].trans_list.number;
    /*@
      @ loop invariant 0 <= i <= num_trans ;
      @ loop invariant \forall integer prei; 0 <= prei < i ==> scsi_automaton[current_state].trans_list.transitions[prei].request != request;
      @ loop assigns i ;
      @ loop variant num_trans - i ;
      */
    for (uint8_t i = 0; i < num_trans; ++i) {
        if (scsi_automaton[current_state].trans_list.transitions[i].request == request) {
            result = true;
            goto err;
        }
    }
    /*@ assert result == \false; */
    /*
     * Didn't find any request associated to current state. This is not a
     * valid transition. We should stall the request.
     */
    log_printf("%s: invalid transition from state %d, request %d\n", __func__,
           current_state, request);
    scsi_set_state(SCSI_ERROR);
    /* @ assert state == SCSI_ERROR; */
err:
    return result;
}
