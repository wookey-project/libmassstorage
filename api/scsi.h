#ifndef SCSI_H
# define SCSI_H

/* SCSI commands */
typedef enum {
    SCSI_CMD_FORMAT_UNIT                   = 0x04, // Mandatory
    SCSI_CMD_INQUIRY			            = 0x12, // Mandatory
    SCSI_CMD_MODE_SELECT_10                = 0x55,
    SCSI_CMD_MODE_SENSE_10	                = 0x5a, // Requiered for some bootable devices
    SCSI_CMD_MODE_SENSE_6                  = 0x1a, // Requiered for some bootable devices
    SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL	= 0x1e,
    SCSI_CMD_READ_10			            = 0x28, // Mandatory
    SCSI_CMD_READ_CAPACITY_10		        = 0x25, // Mandatory
    SCSI_CMD_READ_FORMAT_CAPACITIES        = 0x23,
    SCSI_CMD_REPORT_LUNS                   = 0xa0, // Mandatory
    SCSI_CMD_REQUEST_SENSE			        = 0x03, // Mandatory
    SCSI_CMD_SEND_DIAGNOSTIC               = 0x1d, // Mandatory
    SCSI_CMD_START_STOP_UNIT               = 0x1b,
    SCSI_CMD_SYNCHRONIZE_CACHE_10          = 0x35,
    SCSI_CMD_TEST_UNIT_READY		        = 0x00, // Mandatory
    SCSI_CMD_VERIFY_10                     = 0x2f,
    SCSI_CMD_WRITE_10			            = 0x2a, // Mandatory
} scsi_operation_code_t;

/* SCSI Sense codes */
# define S_NO_SENSE                 0x00
# define S_RECOVERED_ERROR          0x01
# define S_NOT_READY                0x02
# define S_MEDIUM_ERROR             0x03
# define S_HARDWARE_ERROR           0x04
# define S_ILLEGAL_REQUEST          0x05
# define S_UNIT_ATTENTION           0x06
# define S_DATA_PROTECT             0x07
# define S_BLANK_CHECK              0x08
# define S_VENDOR_SPECIFIC          0x09
# define S_COPY_ABORTED             0x0a
# define S_ABORTED_COMMAND          0x0b
# define S_EQUAL                    0x0c
# define S_VOLUME_OVERFLOW          0x0d
# define S_MISCOMPARE               0x0e
# define S_RESERVED                 0x0f

# define ASC_LOGICAL_BLOCK_ADDRESS_OUT_OF_RANGE     0x21
# define ASCQ_LOGICAL_BLOCK_ADDRESS_OUT_OF_RANGE    0x00
# define ASC_MEDIUM_NOT_PRESENT                     0x3a
# define ASCQ_MEDIUM_NOT_PRESENT                    0x00
# define ASC_PERIPHERAL_DEVICE_WRITE_FAULT          0x03
# define ASCQ_PERIPHERAL_DEVICE_WRITE_FAULT         0x00
# define ASC_UNRECOVERED_READ_ERROR                 0x11
# define ASCQ_UNRECOVERED_READ_ERROR                0x00
# define ASC_WRITE_PROTECTED                        0x27
# define ASCQ_WRITE_PROTECTED                       0x00


/* SCSI errors */
# define SCSI_ERROR_GET_SENSE_KEY(error)	((error & 0xf0000) >> 16)
# define SCSI_ERROR_GET_ASC(error)		((error & 0xff00) >> 8)
# define SCSI_ERROR_GET_ASCQ(error)		(error & 0xff)



/**
 * scsi_init - Initialize the USB stack (SCSI, BBB, USB)
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
uint8_t scsi_storage_backend_read(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief Write data to the storage backend
 *
 * \param sector_addr SCSI sector address where the data must be written
 * \param num_sectors number of sectors to write
 *
 * \return 0 on success
 */
uint8_t scsi_storage_backend_write(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief get back the backend storage capacity
 *
 * \param numblock number of SCSI blocks
 * \param blocksize size of one SCSI block
 *
 * \return 0 on success
 */
uint8_t scsi_storage_backend_capacity(uint32_t *numblocks, uint32_t *blocksize);


/***********************************************************
 * libDFU API
 ***********************************************************/


/*
 * Should be two 4096 preallocated sized buffer by now.
 */

uint8_t scsi_early_init(uint8_t*buf, uint16_t buflen);

void scsi_init(void);

void scsi_send_data(void *data, uint32_t size);
void scsi_get_data(void *buffer, uint32_t size);

int scsi_is_ready_for_data(void);
void scsi_send_status(void);

void scsi_exec_automaton(void);

#endif /* SCSI_H */
