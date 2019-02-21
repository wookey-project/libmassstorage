#ifndef SCSI_H
# define SCSI_H

/* SCSI commands */
/* SCSI commands */
# define SCSI_CMD_FORMAT_UNIT                   0x04 // Mandatory
# define SCSI_CMD_INQUIRY			            0x12 // Mandatory
# define SCSI_CMD_MODE_SELECT_6                 0x15
# define SCSI_CMD_MODE_SELECT_10                0x55
# define SCSI_CMD_MODE_SENSE_6			        0x1a
# define SCSI_CMD_MODE_SENSE_10	                0x5a // Requiered for some bootable devices
# define SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL	0x1e
# define SCSI_CMD_READ_6			            0x08 // Mandatory
# define SCSI_CMD_READ_10			            0x28 // Mandatory
# define SCSI_CMD_READ_12			            0xa8
# define SCSI_CMD_READ_CAPACITY_10		        0x25 // Mandatory
# define SCSI_CMD_READ_FORMAT_CAPACITIES        0x23
# define SCSI_CMD_READ_TOC                      0x43
# define SCSI_CMD_REPORT_LUNS                   0xa0 // Mandatory
# define SCSI_CMD_REQUEST_SENSE			        0x03 // Mandatory
# define SCSI_CMD_SEND_DIAGNOSTIC               0x1d // Mandatory
# define SCSI_CMD_START_STOP_UNIT               0x1b
# define SCSI_CMD_SYNCHRONIZE_CACHE_10          0x35
# define SCSI_CMD_TEST_UNIT_READY		        0x00 // Mandatory
# define SCSI_CMD_VERIFY_10                     0x2f
# define SCSI_CMD_WRITE_6			            0x0a // Mandatory
# define SCSI_CMD_WRITE_10			            0x2a // Mandatory
# define SCSI_CMD_WRITE_12                      0xaa

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
# define SCSI_ERROR_INVALID_COMMAND		0x52000
# define SCSI_ERROR_UNIT_BECOMING_READY		((0x2 << 16) | (0x04 << 8) | 0x01)


/**
 * scsi_init - Initialize the USB stack (SCSI, BBB, USB)
 */

/*!
 * Callbacks that handle upper layer effective read or write request to
 * local (or remote application) storage access request. This callbacks
 * must be blocking callbacks while the transaction is not finished yet
 * (i.e. the data read or data write is not effective).
 */
typedef uint8_t (*scsi_read_cb)(uint32_t sector_addr, uint32_t num_sectors);
typedef uint8_t (*scsi_write_cb)(uint32_t sector_addr, uint32_t num_sectors);

/*
 * Should be two 4096 preallocated sized buffer by now.
 */
uint8_t scsi_early_init(uint8_t*buf, uint16_t buflen, scsi_read_cb read_cb, scsi_write_cb write_cb);
void scsi_init(void);

void scsi_send_data(void *data, uint32_t size);
void scsi_get_data(void *buffer, uint32_t size);

/*
 * id_data_sink: the target task of the usb data content (write mode)
 * id_data_source: the source of the usb data content (read mode)
 */
void scsi_state_machine(uint8_t id_data_sink, uint8_t id_data_source);

int scsi_is_ready_for_data(void);
void scsi_send_status(void);

#endif /* SCSI_H */
