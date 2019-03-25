#include "api/malloc.h"
#include "api/stdio.h"
#include "api/nostd.h"
#include "api/string.h"
#include "api/scsi.h"
#include "api/string.h"
#include "usb.h"
#include "usb_bbb.h"
#include "queue.h"
#include "debug.h"
#include "autoconf.h"
#include "api/syscall.h"
#include "wookey_ipc.h"
#include "scsi_cmd.h"

#define assert(val) if (!(val)) { while (1) ; };

#define SCSI_DEBUG 0




typedef enum scsi_state {
    SCSI_IDLE = 0x00,
    SCSI_READ,
    SCSI_WRITE,
    SCSI_ERROR,
} scsi_state_t;

/*
 * The SCSI stack context. This is a global variable, which means
 * that the SCSI stack is not reentrant (not for scsi_context write access).
 * As most micro-controlers are not multicore based, this should not be
 * a problem.
 */
typedef enum {
   SCSI_TRANSMIT_LINE_READY = 0,
   SCSI_TRANSMIT_LINE_BUSY,
   SCSI_TRANSMIT_LINE_ERROR,
} transmition_line_state_t;

typedef enum {
    SCSI_DIRECTION_IDLE = 0,
    SCSI_DIRECTION_SEND,
    SCSI_DIRECTION_RECV,
} transmission_direction_t;

typedef enum {
    SCSI_ERROR_NONE = 0,
    SCSI_ERROR_CHECK_CONDITION = 0x02, /* FIXME: encoded value to set */
    SCSI_ERROR_UNIT_BECOMING_READY = 0x20401,
    SCSI_ERROR_INVALID_COMMAND = 0x52000,

} scsi_error_t;


typedef  struct {
    volatile transmission_direction_t direction;
    volatile transmition_line_state_t line_state;
    volatile uint32_t size_to_process;
    uint32_t addr;
    scsi_error_t error;
    struct queue *queue;
    bool queue_empty;
    uint8_t *global_buf;
    uint16_t global_buf_len;
    scsi_state_t state;
    uint32_t block_size;
    uint32_t storage_size;
} scsi_context_t;


scsi_context_t scsi_ctx = {
    .direction = SCSI_DIRECTION_IDLE,
    .line_state = SCSI_TRANSMIT_LINE_READY,
    .size_to_process = 0,
    .addr = 0,
    .error= 0,
    .queue=NULL,
    .queue_empty = true,
    .global_buf = NULL,
    .state = SCSI_IDLE,
    .global_buf_len = 0,
    .block_size = 0,
    .storage_size = 0,
};






/****************************************************************
 * SCSI state automaton formal definition and associate utility
 * functions
 ***************************************************************/

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

# define MAX_TRANSITION_STATE 15

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
                                {SCSI_CMD_READ_10,SCSI_IDLE},
                                {SCSI_CMD_READ_CAPACITY_10,SCSI_IDLE},
                                {SCSI_CMD_READ_CAPACITY_16,SCSI_IDLE},
                                {SCSI_CMD_READ_FORMAT_CAPACITIES,SCSI_IDLE},
                                {SCSI_CMD_REPORT_LUNS,SCSI_IDLE},
                                {SCSI_CMD_REQUEST_SENSE,SCSI_IDLE},
                                {SCSI_CMD_SEND_DIAGNOSTIC,SCSI_IDLE},
                                {SCSI_CMD_TEST_UNIT_READY,SCSI_IDLE},
                                {SCSI_CMD_WRITE_10,SCSI_IDLE},
                             }
    },
    { SCSI_READ,     {
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

static inline scsi_state_t scsi_get_state() {
    return scsi_ctx.state;
}


/*
 * This function is eligible in both main thread and ISR
 * mode (through trigger execution). Please use aprintf only
 * here.
 */
static inline void scsi_set_state(const scsi_state_t new_state)
{
    if (new_state == 0xff) {
        aprintf("%s: PANIC! this should never arise !", __func__);
        while (1) {}; //FIXME
        return;
    }
#if SCSI_DEBUG
    aprintf("%s: state: %x => %x\n", __func__, scsi_ctx.state, new_state);
#endif
    scsi_ctx.state = new_state;
}

void scsi_error(scsi_error_t reason){
#if SCSI_DEBUG
    aprintf("%s: %s: status=%d\n", __func__, __func__, reason);
    aprintf("%s: state -> Error\n",__func__);
#endif
    scsi_ctx.error = reason;
    usb_bbb_send_csw(CSW_STATUS_FAILED, 0);
    scsi_set_state(SCSI_IDLE);
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
static uint8_t scsi_next_state(scsi_state_t  current_state, scsi_operation_code_t    request)
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
static bool scsi_is_valid_transition(scsi_state_t current_state,
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

/*********************************************************************
 * Mutexes, protection against race conditions...
 ********************************************************************/

/*
 * \brief entering a critical section
 *
 * During this critical section, any ISR is postponed to avoid any
 * race condition on variables shared in write-access between ISR and
 * main thread. See sys_lock() syscall API documentation.
 *
 * Critical sections must be as short as possible to avoid border
 * effects such as latency increase and ISR queue overloading.
 */
static inline void enter_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_ENTER); /* Enter in critical section */
    if(ret != SYS_E_DONE){
        printf("%s: Error: failed entering critical section!\n", __func__);
    }
    return;
}

/*
 * \brief leaving a critical section
 *
 * Reallow the execution of the previously postponed task ISR.
 */
static inline void leave_critical_section(void)
{
    uint8_t ret;
    ret = sys_lock (LOCK_EXIT);  /* Exit from critical section */
    if(ret != SYS_E_DONE){
        printf("Error: failed exiting critical section!\n");
    }
    return;
}

/****************** END OF AUTOMATON *********************/

typedef struct  __attribute__((packed)){
     uint8_t reserved1:3;
     uint8_t LLBAA:2;
     uint8_t DBD:2;
     uint8_t reserved2:1;
     uint8_t PC:2;
     uint8_t page_code:6;
     uint8_t sub_page_code;
     uint16_t reserved3;
     uint16_t allocation_length;
     uint8_t control;
} cdb10_mode_sense_t;


typedef struct  __attribute__((packed)){
     uint16_t reserved1;
     uint8_t reserved2:6;
     uint8_t prevent:2;
     uint8_t control;
} cdb10_prevent_allow_removal_t;

typedef struct  __attribute__((packed)){
     uint8_t reserved1:7;
     uint8_t desc:1;
     uint16_t reserved;
     uint8_t allocation_length;
} cdb10_request_sense_t;

typedef struct  __attribute__((packed)){
     uint8_t misc1:3;
     uint8_t service_action:5;
     uint32_t logical_block;
     uint8_t misc2;
     uint16_t transfer_blocks;
     uint8_t control;
} cdb10_t;

typedef struct  __attribute__((packed)){
     uint8_t LUN:3;
     uint8_t reserved4:1;
     uint8_t DBD:1;
     uint8_t reserved3:3;
     uint8_t PC:2;
     uint8_t page_code:6;
     uint8_t reserved2;
     uint8_t allocation_length;
     uint8_t vendor_specific:2;
     uint8_t reserved1:4;
     uint8_t flag:1;
     uint8_t link:1;
} cdb6_mode_sense_t;


typedef struct __attribute__((packed)) {
    uint8_t  reserved3:3;
    uint8_t  PF:1;
    uint8_t  reserved2:2;
    uint8_t  RTD:1;
    uint8_t  SP:1;
    uint16_t reserved1;
    uint8_t  parameter_list_length;
    uint8_t  control;
} cdb6_mode_select_t;


typedef struct __attribute__((packed)) {
    uint8_t  reserved:6;
    uint8_t  CMDDT:1; /* obsolete */
    uint8_t  EVPD:1;
    uint8_t  page_code;
    uint16_t allocation_length;
    uint8_t  control;
} cdb6_inquiry_t;

typedef struct __attribute__((packed)) {
    uint8_t  reserved3:3;
    uint8_t  PF:1;
    uint8_t  reserved2:3;
    uint8_t  SP:1;
    uint8_t  reserved1_bis;
    uint32_t reserved1;
    uint16_t  parameter_list_length;
    uint8_t  control;
} cdb10_mode_select_t;

typedef struct __attribute__((packed)) {
    uint8_t  reserved3;
    uint8_t  selected_report;
    uint16_t reserved2_2;
    uint8_t  reserved2_1;
    uint32_t allocation_length;
    uint8_t  reserved1;
    uint8_t  control;
} cdb12_report_luns_t;



typedef struct  __attribute__((packed)){
    uint8_t  Reserved2:3;
    uint8_t  service_action:5;
    uint64_t logical_block_address;
    uint32_t allocation_length;
    uint8_t  Reserved1:7;
    uint8_t  PMI:1;
    uint8_t  control;
} cdb16_read_capacity_16_t;

typedef union {
    /* CDB 6 bytes length */
    cdb6_mode_sense_t              cdb6_mode_sense;
    cdb6_mode_select_t             cdb6_mode_select;
    cdb6_inquiry_t                 cdb6_inquiry;
    /* CDB 10 bytes length */
    cdb10_t                        cdb10; /* read and write */
    cdb10_mode_sense_t             cdb10_mode_sense;
    cdb10_mode_select_t            cdb10_mode_select;
    cdb10_prevent_allow_removal_t  cdb10_prevent_allow_removal;
    cdb10_request_sense_t          cdb10_request_sense;
    /* CDB 12 bytes length */
    cdb12_report_luns_t            cdb12_report_luns;
    /* CDB 16 bytes length */
    cdb16_read_capacity_16_t       cdb16_read_capacity;
} u_cdb_payload;

typedef  struct  __attribute__((packed)){
    uint8_t operation;
    u_cdb_payload payload;
} cdb_t;



/***************************
 * about responses
 **************************/

typedef struct __attribute__((packed)) {
    uint32_t ret_lba;
    uint32_t ret_block_length;
} read_capacity10_parameter_data_t;

typedef struct __attribute__((packed)) {
    uint64_t ret_lba;
    uint32_t ret_block_length;
    uint8_t  reserved2:2;
    uint8_t  rc_basis:2;
    uint8_t  p_type:3;
    uint8_t  prot_enable:1;
    uint8_t  p_i_expornent:4;
    uint8_t  logical_block_per_phys_block_component:4;
    uint16_t lbpme:1;
    uint16_t lbprz:1;
    uint16_t lowest_aligned_lba:14;
    uint8_t  reserved1[16];
} read_capacity16_parameter_data_t;


typedef struct  __attribute__((packed)) {
    uint16_t mode_data_length;
    uint8_t medium_type;
    uint8_t device_specific_param;
    uint8_t reserved1:7;
    uint8_t longLBA:1;
    uint8_t reserved2;
    uint16_t block_descriptor_length;
} mode_parameter_header_t;

typedef struct __packed request_sense_parameter_data {
   uint8_t error_code:7;
   uint8_t info_valid:1;
   uint8_t reserved1;
   uint8_t sense_key:4;
   uint8_t reserved:1;
   uint8_t ili:1;
   uint8_t eom:1;
   uint8_t filemark:1;
   uint8_t information[4];
   uint8_t additional_sense_length;
   uint32_t reserved8;
   uint8_t asc;
   uint8_t ascq;
   uint8_t field_replaceable_unit_code;
   uint8_t sense_key_specific[3];
} request_sense_parameter_data_t;


typedef struct  __attribute__((packed)) {
    uint32_t lun_list_length;
    uint32_t reserved;
    uint64_t  luns[];
} report_luns_data_t;

typedef struct __packed inquiry_data {
	uint8_t   periph_qualifier:3;
	uint8_t   periph_device_type:5;
	uint8_t   RMB:1;
	uint8_t   reserved3:7;
	uint8_t   version;
	uint8_t   obsolete4:2;
	uint8_t   NORMACA:1;
	uint8_t   HISUP:1;
	uint8_t   data_format:4;
	uint8_t   additional_len;
	uint8_t   SCCS:1;
	uint8_t   ACC:1;
	uint8_t   TPGS:2;
	uint8_t   TPC:1;
	uint8_t   reserved2:2;
	uint8_t   PROTECT:1;
	uint8_t   obsolete3:1;
	uint8_t   ENCSERV:1;
	uint8_t   VS2:1;
	uint8_t   multip:1;
	uint8_t   obsolete2:4;
	uint8_t   obsolete1:6;
	uint8_t   CMDQUE:1;
	uint8_t   VS1:1;
	char      vendor_info[8];
	char      product_identification[16];
	char      product_revision[4];
    uint64_t  drive_serial_number;
    uint8_t   vendor_unique[12];
    uint8_t   reserved1;
    uint16_t  version_descriptor[8];
    /*reserved: bytes 74->95 */
    /* copyright notice: 96->n */

} inquiry_data_t;





static void scsi_release_cdb(cdb_t * current_cdb){

	if(current_cdb != NULL){
        enter_critical_section();
		if(wfree((void**)&current_cdb)){
			while(1){}; // FIXME
		}
        leave_critical_section();
	}
	current_cdb = NULL;
}

static inline bool scsi_is_ready_for_data_receive(void)
{
    return (   (   scsi_ctx.direction == SCSI_DIRECTION_RECV
                || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY );
}

static inline bool scsi_is_ready_for_data_send(void)
{
    return (   (   scsi_ctx.direction == SCSI_DIRECTION_SEND
                || scsi_ctx.direction == SCSI_DIRECTION_IDLE)
            && scsi_ctx.line_state == SCSI_TRANSMIT_LINE_READY );
}



void scsi_get_data(void *buffer, uint32_t size)
{
#if SCSI_DEBUG
	printf("%s: size: %d \n", __func__, size );
#endif
	while(!scsi_is_ready_for_data_receive()){
		continue;
	}

	scsi_ctx.direction = SCSI_DIRECTION_RECV;
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_BUSY;
	scsi_ctx.size_to_process = size;
    scsi_ctx.addr = 0;

	usb_bbb_read(buffer, size, 1);
}


void scsi_send_data(void *data, uint32_t size)
{
#if SCSI_DEBUG
	printf("%s: size: %d \n", __func__, size );
#endif

	scsi_ctx.direction = SCSI_DIRECTION_SEND;
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_BUSY;
    scsi_ctx.addr = 0;

	usb_bbb_send(data, size, 2); // FIXME HARCODED ENDPOINT
}

/*
 * Trigger on input data available
 */
static void scsi_data_available(uint32_t size)
{
#if SCSI_DEBUG
    aprintf("%s: %d\n", __func__, size);
#endif

    if (size >= scsi_ctx.size_to_process) {
        scsi_ctx.size_to_process = 0;
    } else {
        scsi_ctx.size_to_process -= size;
    }
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;

    if (scsi_ctx.size_to_process == 0){
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        scsi_ctx.direction = SCSI_DIRECTION_IDLE;
        scsi_set_state(SCSI_IDLE);
    }
}


/*
 * Trigger on data sent by IP
 */
static void scsi_data_sent(void)
{
#if SCSI_DEBUG
    aprintf("%s\n", __func__);
#endif

    if (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_ctx.size_to_process -= scsi_ctx.global_buf_len;
    } else {
        scsi_ctx.size_to_process = 0;
    }
    scsi_ctx.line_state = SCSI_TRANSMIT_LINE_READY;

    if (scsi_ctx.size_to_process == 0) {
        usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
        scsi_ctx.direction = SCSI_DIRECTION_IDLE;
        scsi_set_state(SCSI_IDLE);
    }
}


/* NB: this function is executed in a handler context when a
 * command comes from USB.
 */
static void scsi_parse_cdb(uint8_t cdb[], uint8_t cdb_len __attribute__((unused)))
{
    cdb_t *current_cdb;
	int ret;

    // Only 10 byte commands are supported, bigger sized commands are trunccated
    ret = wmalloc((void**)&current_cdb, sizeof(cdb_t), ALLOC_NORMAL);
    if(ret){
        scsi_set_state(SCSI_ERROR);
    }

    memcpy((void *)current_cdb, (void *)cdb, sizeof(cdb_t));

	queue_enqueue(scsi_ctx.queue, current_cdb);
	scsi_ctx.queue_empty = 0;
}









/*
 * Commands
 */

static void scsi_cmd_inquiry(scsi_state_t  current_state, cdb_t * cdb)
{
	inquiry_data_t response;
    cdb6_inquiry_t *inq;

#if SCSI_DEBUG
		printf("%s:\n", __func__ );
#endif
    /* Sanity check */
    if(cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, cdb->operation);

    if (!scsi_is_valid_transition(current_state, cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, cdb->operation);

    /* effective transition execution (if needed) */
    inq = &(cdb->payload.cdb6_inquiry);


#if 1
    printf("inquiry:\n");
    printf("CMDDT:         %x\n", inq->CMDDT);
    printf("EVPD:          %x\n", inq->EVPD);
    printf("page_code:     %x\n", inq->page_code);
    printf("allocation_len:%x\n", from_big16(inq->allocation_length));
    printf("control  :     %x\n", inq->control);
#endif

    /* sanitize received cmd in conformity with SCSI standard */
    if (inq->EVPD == 0 && from_big16(inq->allocation_length) < 5) {
        /* invalid: additional fields parameter can't be send */
        goto invalid_cmd;
    }

    if (inq->EVPD == 1 && from_big16(inq->allocation_length) < 4) {
        /* invalid: additional fields parameter can't be send */
        goto invalid_cmd;
    }

	/* Most of support bits are set to 0
	 * version is 0 because the device does not claim conformance to any
	 * standard
	 */
	memset((void *)&response, 0, sizeof(response));

    response.periph_device_type = 0x0; /* direct access block device */
	response.RMB = 1;                           /* Removable media */

	response.data_format = 2;                   /* < 2 obsoletes, > 2 reserved */
	response.additional_len = sizeof(response) - 5; /* (36 - 5) bytes after this one remain */
    response.additional_len = sizeof(response) - 5; /* (36 - 5) bytes after this one remain */

    /* empty char must be set with spaces */
    memset(response.vendor_info, 0x20, sizeof(response.vendor_info));
    memcpy(response.vendor_info, CONFIG_USB_DEV_MANUFACTURER, sizeof(response.vendor_info));
    /* empty char must be set with spaces */
    memset(response.product_identification, 0x20, sizeof(response.product_identification));
    memcpy(response.product_identification, CONFIG_USB_DEV_PRODNAME, sizeof(response.product_identification));

    memcpy(response.product_revision, CONFIG_USB_DEV_REVISION, sizeof(response.product_revision));

#if SCSI_DEBUG
    printf("%s: %s\n",__func__, response.product_revision);
#endif


    if (inq->allocation_length > 0) {
        usb_bbb_send((uint8_t *)&response, (from_big16(inq->allocation_length) < sizeof(response)) ? from_big16(inq->allocation_length) : sizeof(response), 2);
    } else {
        printf("allocation length is 0\n");
    }
    return;

invalid_cmd:
    printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


static void scsi_cmd_prevent_allow_medium_removal(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);
#if SCSI_DEBUG
    printf("%s: Prevent allow medium removal: %x\n",__func__, current_cdb->payload.cdb10_prevent_allow_removal.prevent);
#endif
    // FIXME Add callback ?
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;
    /* effective transition execution (if needed) */

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


// SCSI_CMD_READ_10
static void scsi_cmd_read_data10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;
    uint32_t total_num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request READ10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_ERROR_INVALID_COMMAND);
        return;
    }

    /* entering READ state... */
    next_state = scsi_next_state(current_state, current_cdb->operation);
    scsi_set_state(next_state);

    rw_lba = from_big32(current_cdb->payload.cdb10.logical_block);
    rw_size = from_big16(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;
    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;

    total_num_sectors = scsi_ctx.size_to_process / scsi_ctx.block_size;
    #if SCSI_DEBUG
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
    #endif


    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        /* There is more data to send that the buffer is able to process,
         * data are sent in multiple chunks of buf_len size... */

        /* INFO: num_sectors may be defined out of the loop */
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        scsi_storage_backend_read(rw_lba, num_sectors);
        /* send data we have just read */
		scsi_send_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        /* increment read pointer */
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {
#if SCSI_DEBUG
        printf("%s: sending data residue to host.\n", __func__);
#endif
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        scsi_storage_backend_read((uint32_t)rw_lba, num_sectors);
        scsi_send_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
#if SCSI_DEBUG
        #endif
        /* active wait for data to be sent */
        while(!scsi_is_ready_for_data_send()){
            continue;
        }
    }

    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}



// FIXME SCSI_CMD_READ_CAPACITY_10
static void scsi_cmd_read_capacity10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity10_parameter_data_t response;
    uint8_t ret;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);


    /* let's get capacity from upper layer */
    ret = scsi_storage_backend_capacity(&(scsi_ctx.storage_size), &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_ERROR_UNIT_BECOMING_READY);
        return;
    }

    //what is expected is the _LAST_ LBA address ....
    // See Working draft SCSI block cmd  5.10.2 READ CAPACITY (10)

	response.ret_lba = to_big32(scsi_ctx.storage_size-1);
	response.ret_block_length = to_big32(scsi_ctx.block_size);

    usb_bbb_send((uint8_t *)&response, sizeof(read_capacity10_parameter_data_t), 2);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}

static void scsi_cmd_read_capacity16(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint8_t next_state;
    read_capacity16_parameter_data_t response;
    cdb16_read_capacity_16_t *rc16;
    uint8_t ret;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);


    /* let's get capacity from upper layer */
    ret = scsi_storage_backend_capacity(&(scsi_ctx.storage_size), &(scsi_ctx.block_size));
    if (ret != 0) {
        /* unable to get back capacity from backend... */
        scsi_error(SCSI_ERROR_UNIT_BECOMING_READY);
        return;
    }

    /* get back cdb content from union */
    rc16 = &(current_cdb->payload.cdb16_read_capacity);

    //what is expected is the _LAST_ LBA address ....
    // See Working draft SCSI block cmd  5.10.2 READ CAPACITY (16)

    /* creating response... */
    memset((void*)&response, 0x0, sizeof(read_capacity16_parameter_data_t));
	response.ret_lba = (uint64_t)to_big32(scsi_ctx.storage_size-1);
	response.ret_block_length = to_big32(scsi_ctx.block_size);
    response.prot_enable = 0; /* no prot_enable, protection associated fields
                                 are disabled. */
    response.rc_basis = 0x01; /* LBA is the LBA of the last logical block
                                 on the logical unit. See Seagate SCSI
                                 command ref., chap. 3.23.2 */

    #if SCSI_DEBUG
        printf("%s: response[0]: %d response[1]: %d\n", __func__, response[0], response[1]);
    #endif

    /* the amount of bytes sent in the response depends on the allocation
     * length value set in the read_capacity16 cmd. If this value is null,
     * no response should be sent.
     * See Seagate SCSI command ref. chap. 3.23.2 */
    if (rc16->allocation_length > 0) {
        usb_bbb_send((uint8_t *)&response, (rc16->allocation_length < sizeof(response)) ? rc16->allocation_length : sizeof(response), 2);
    }
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


// FIXME SCSI_CMD_REPORT_LUNS
static void scsi_cmd_report_luns(scsi_state_t  current_state, cdb_t * current_cdb)
{
    cdb12_report_luns_t *rl;
    bool check_condition = false;
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (next_state != 0xff) {
        scsi_set_state(next_state);
    } else {
        goto invalid_transition;
    }

    rl = &(current_cdb->payload.cdb12_report_luns);

    if (from_big16(rl->allocation_length) < 16) {
        /* invalid: requested to be at least 16 by standard */
        goto invalid_cmd;
    }
    if (from_big16(rl->allocation_length) < 24) {
        /* enable to send first lun informations */
        check_condition = true;
    }


    // TODO We only support 1 LUN
    report_luns_data_t response = {
        .lun_list_length = 1,
        .reserved = 0,
    };
    response.luns[0] = 0;

    /* sending response, up to required bytes */
    usb_bbb_send((uint8_t *)&response, (from_big16(rl->allocation_length) < sizeof(response)) ? from_big16(rl->allocation_length) : sizeof(response), 2);

    /* if the host didn't reserve enough space to respond, inform it that
     * some informations are missing */
    if (check_condition) {
        usb_bbb_send_csw(SCSI_ERROR_CHECK_CONDITION, 0);
    }
    return;

    /* XXX
     * If the logical unit inventory changes for any reason
     * (e.g., completion of initialization, removal of a logical unit, or creation of a logical unit),
     * then the device server shall establish a unit attention condition (see SAM-3) for the
     * initiator port associated with every I_T nexus, with the additional sense code set
     * to REPORTED LUNS DATA HAS CHANGED.
     */


invalid_cmd:
    printf("%s: malformed cmd\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}

static void scsi_cmd_request_sense(scsi_state_t  current_state, cdb_t * current_cdb)
{
    request_sense_parameter_data_t data;

    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

#if SCSI_DEBUG
    printf( "%s: desc: %x, allocation_length: %x\n",
            current_cdb->payload.cdb10_request_sense.desc,
            current_cdb->payload.cdb10_request_sense.allocation_length);
#endif

    // TODO If desc is set to 1 and descriptor format sense data is supported
    // descriptor format sense data shall be returned.

	memset((void *)&data, 0, sizeof(data));
	data.error_code = 0x70;
	data.sense_key = SCSI_ERROR_GET_SENSE_KEY(scsi_ctx.error);
	data.additional_sense_length = 0x0a;
	data.asc = SCSI_ERROR_GET_ASC(scsi_ctx.error);
	data.ascq = SCSI_ERROR_GET_ASCQ(scsi_ctx.error);
	usb_bbb_send((uint8_t *)&data, sizeof(data), 2);
    return;


invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}

static void scsi_cmd_mode_sense10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    printf("%s:\n", __func__);
    printf("\treserved1          : %x\n", current_cdb->payload.cdb10_mode_sense.LLBAA);
    printf("\tLLBAA              : %x\n", current_cdb->payload.cdb10_mode_sense.LLBAA);
    printf("\tDBD                : %x\n", current_cdb->payload.cdb10_mode_sense.DBD);
    printf("\treserved2          : %x\n", current_cdb->payload.cdb10_mode_sense.reserved2);
    printf("\tPC                 : %x\n", current_cdb->payload.cdb10_mode_sense.PC);
    printf("\tpage_code          : %x\n", current_cdb->payload.cdb10_mode_sense.page_code);
    printf("\tsub_page_code      : %x\n", current_cdb->payload.cdb10_mode_sense.sub_page_code);
    printf("\treserved3          : %x\n", current_cdb->payload.cdb10_mode_sense.reserved3);
    printf("\tallocation_length  : %x\n", current_cdb->payload.cdb10_mode_sense.allocation_length);
    printf("\tcontrol            : %x\n", current_cdb->payload.cdb10_mode_sense.control);

    /* Sending Mode Sense 10 answer */
    /* We only send back the mode parameter header with no data */
    mode_parameter_header_t mode_sens_header = {
        .mode_data_length = 3,        // The number of bytes that follow.
        .medium_type = 0,             // The media type SBC.
        .device_specific_param = 0,   // Not write proectected (bit:7), no cache control-bit support (bit:4).
        .reserved1 = 0,
        .longLBA = 0,
        .reserved2  = 0,
        .block_descriptor_length = 0, // A block descriptor length of zero indicates that no block descriptors
                                      // are included in the mode parameter list.
    };

    //usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t));
    usb_bbb_send((uint8_t *)&mode_sens_header, sizeof(mode_parameter_header_t), 2);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


static void scsi_cmd_mode_sense6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

#if 0
    printf("%s:\n", __func__);
    printf("\tLUN                : %x\n", current_cdb->payload.cdb6_mode_sense.LUN);
    printf("\treserved4          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved4);
    printf("\tDBD                : %x\n", current_cdb->payload.cdb6_mode_sense.DBD);
    printf("\treserved3          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved3);
    printf("\tPC                 : %x\n", current_cdb->payload.cdb6_mode_sense.PC);
    printf("\tpage_code          : %x\n", current_cdb->payload.cdb6_mode_sense.page_code);
    printf("\treserved2          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved2);
    printf("\tallocation_length  : %x\n", current_cdb->payload.cdb6_mode_sense.allocation_length);
    printf("\tvendor_specific    : %x\n", current_cdb->payload.cdb6_mode_sense.vendor_specific);
    printf("\treserved1          : %x\n", current_cdb->payload.cdb6_mode_sense.reserved1);
    printf("\tflag               : %x\n", current_cdb->payload.cdb6_mode_sense.flag);
    printf("\tlink               : %x\n", current_cdb->payload.cdb6_mode_sense.link);
#endif

    /* Sending Mode Sense 10 answer */
    /* We only send back the mode parameter header with no data */
    mode_parameter_header_t mode_sens_header = {
        .mode_data_length = 3,        // The number of bytes that follow.
        .medium_type = 0,             // The media type SBC.
        .device_specific_param = 0,   // Not write proectected (bit:7), no cache control-bit support (bit:4).
        .reserved1 = 0,
        .longLBA = 0,
        .reserved2  = 0,
        .block_descriptor_length = 0, // A block descriptor length of zero indicates that no block descriptors
                                      // are included in the mode parameter list.
    };

    //usb_bbb_send_csw(CSW_STATUS_SUCCESS, sizeof(mode_parameter_header_t));
    usb_bbb_send((uint8_t *)&mode_sens_header, sizeof(mode_parameter_header_t), 2);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}

static void scsi_cmd_mode_select6(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


static void scsi_cmd_mode_select10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


// FIXME SCSI_CMD_TEST_UNIT_READY
static void scsi_cmd_test_unit_ready(scsi_state_t  current_state, cdb_t * current_cdb)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* Sanity check */
    if(current_cdb == NULL){
        printf("%s: current_cdb == NULL\n", __func__);
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    /* effective transition execution (if needed) */
    usb_bbb_send_csw(CSW_STATUS_SUCCESS, 0);
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}

// FIXME SCSI_CMD_WRITE_10
static void scsi_write_data10(scsi_state_t  current_state, cdb_t * current_cdb)
{
    uint32_t num_sectors;

    uint32_t rw_lba;
    uint16_t rw_size;
    uint64_t rw_addr;

#if SCSI_DEBUG
    printf("%s:\n",__func__);
#endif

	if(current_cdb == NULL){
		return;
	}

    /* Sanity check */
    if(current_cdb == NULL){
        goto invalid_transition;
    }

    /* Sanity check and next state detection */
    uint8_t next_state;
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (!scsi_is_valid_transition(current_state, current_cdb->operation)) {
        goto invalid_transition;
    }
    next_state = scsi_next_state(current_state, current_cdb->operation);

    if (next_state != 0xff) {
        scsi_set_state(next_state);
    } else {
        goto invalid_transition;
    }

    /* SCSI standard says that the host should not request WRITE10 cmd
     * before requesting GET_CAPACITY cmd. In this very case, we have to
     * send back INVALID to the host */
    if (scsi_ctx.storage_size == 0) {
        scsi_error(SCSI_ERROR_INVALID_COMMAND);
        return;
    }


    rw_lba = from_big32(current_cdb->payload.cdb10.logical_block);
    rw_size = from_big16(current_cdb->payload.cdb10.transfer_blocks);
    rw_addr  = (uint64_t)scsi_ctx.block_size * (uint64_t)rw_lba;

    /* initialize size_to_process. This variable will be upated during the
     * active wait loop below by the USB BBB triggers (usb_data_sent for
     * read, usb_data_available for write */
    scsi_ctx.size_to_process = scsi_ctx.block_size * rw_size;


#if SCSI_DEBUG
    uint32_t total_num_sectors = rw_size;
    printf("%s: sz %u, block_size: %u | num_sectors: %u\n", __func__, scsi_ctx.size_to_process, scsi_ctx.block_size, total_num_sectors);
#endif

    while (scsi_ctx.size_to_process > scsi_ctx.global_buf_len) {
        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.global_buf_len);
        while(!scsi_is_ready_for_data_receive()) {
            continue;
        }
        num_sectors = scsi_ctx.global_buf_len / scsi_ctx.block_size;
        scsi_storage_backend_write(rw_lba, num_sectors);
        rw_lba += scsi_ctx.global_buf_len / scsi_ctx.block_size;
    }

    /* Fractional residue */
    if (scsi_ctx.size_to_process > 0) {

        scsi_get_data(scsi_ctx.global_buf, scsi_ctx.size_to_process);
        /* num_sectors *must* be calculated before waiting for ISR, as
         * the ISR trigger decrement size_to_process */
        num_sectors = (scsi_ctx.size_to_process) / scsi_ctx.block_size;
        while(!scsi_is_ready_for_data_receive()){
            continue;
        }
        scsi_storage_backend_write(rw_lba, num_sectors);
    }
    return;

invalid_transition:
    printf("%s: invalid_transition\n", __func__);
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


void scsi_exec_automaton(void)
{
    cdb_t * current_cdb = NULL;

    enter_critical_section();
	if(scsi_ctx.queue_empty == 1){
        leave_critical_section();
        return;
    }
    current_cdb = queue_dequeue(scsi_ctx.queue);
    if(queue_is_empty(scsi_ctx.queue)){
        scsi_ctx.queue_empty = 1;
    }
    leave_critical_section();

    scsi_state_t current_state = scsi_get_state();

	switch (current_cdb->operation) {
	case SCSI_CMD_INQUIRY:
		scsi_cmd_inquiry(current_state, current_cdb);
		break;

	case SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL:
		scsi_cmd_prevent_allow_medium_removal(current_state, current_cdb);
		break;

	case SCSI_CMD_READ_10:
		scsi_cmd_read_data10(current_state, current_cdb);
		break;

	case SCSI_CMD_READ_CAPACITY_10:
		scsi_cmd_read_capacity10(current_state, current_cdb);
		break;

	case SCSI_CMD_READ_CAPACITY_16:
		scsi_cmd_read_capacity16(current_state, current_cdb);
		break;

	case SCSI_CMD_REPORT_LUNS:
		scsi_cmd_report_luns(current_state, current_cdb);
		break;

    case SCSI_CMD_MODE_SELECT_10:
           scsi_cmd_mode_select10(current_state, current_cdb);
           break;

    case SCSI_CMD_MODE_SELECT_6:
           scsi_cmd_mode_select6(current_state, current_cdb);
           break;

    case SCSI_CMD_MODE_SENSE_10:
           scsi_cmd_mode_sense10(current_state, current_cdb);
           break;

    case SCSI_CMD_MODE_SENSE_6:
           scsi_cmd_mode_sense6(current_state, current_cdb);
           break;


    case SCSI_CMD_REQUEST_SENSE:
           scsi_cmd_request_sense(current_state, current_cdb);
           break;
#if 0
	case SCSI_CMD_SEND_DIAGNOSTIC:
		scsi_cmd_send_diagnostic(current_state, current_cdb);
		break;
#endif
	case SCSI_CMD_TEST_UNIT_READY:
		scsi_cmd_test_unit_ready(current_state, current_cdb);
		break;

	case SCSI_CMD_WRITE_10:
		scsi_write_data10(current_state, current_cdb);
		break;

	default:
        goto invalid_command;
	};

    scsi_release_cdb(current_cdb);
    return;

invalid_command:
#if SCSI_DEBUG
    printf("%s: Unsupported command: %x  \n", __func__, current_cdb->operation);
#endif
    scsi_error(SCSI_ERROR_INVALID_COMMAND);
    return;
}


typedef enum scsi_init_error {
    SCSI_INIT_DONE = 0x00,
    SCSI_INIT_CALLBACK_ERROR,
    SCSI_INIT_BUFFER_ERROR,
} scsi_init_error_t;


uint8_t scsi_early_init(uint8_t *buf, uint16_t len)
{

    scsi_init_error_t error = -1;
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    if ( !buf ) {
        error = SCSI_INIT_BUFFER_ERROR;
        goto init_error;
    }

    if ( len <= 0 ) {
        error = SCSI_INIT_BUFFER_ERROR;
        goto init_error;
    }

    scsi_ctx.global_buf = buf;
    scsi_ctx.global_buf_len = len;

	usb_bbb_early_init(scsi_parse_cdb, scsi_data_available, scsi_data_sent);
    return 0;

init_error:
#if SCSI_DEBUG
    printf("%s: ERROR: Unable to initialize scsi stack : %x  \n", __func__, error);
#endif
    return 1;
}

/*
 * Init
 */
#define MAX_SCSI_CMD_QUEUE_SIZE 10

void scsi_init(void)
{
    #if SCSI_DEBUG
        printf("%s\n", __func__);
    #endif

    /* in USB High speed mode, the USB device is mapped (and enabled) just now */
    usb_driver_map();

	unsigned int i;

    scsi_ctx.storage_size = 0;
    scsi_ctx.block_size = 4096; /* default */

	scsi_ctx.queue = queue_create(MAX_SCSI_CMD_QUEUE_SIZE);

	for(i = 0; i < scsi_ctx.global_buf_len; i++){
		scsi_ctx.global_buf[i] = i;
	}

	/* Register our callbacks on the lower layer */
	usb_bbb_init();

    scsi_set_state(SCSI_IDLE);
}


