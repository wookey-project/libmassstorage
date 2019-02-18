#ifndef SCSI_H
# define SCSI_H

/* SCSI commands */
# define SCSI_CMD_TEST_UNIT_READY		0x00
# define SCSI_CMD_REQUEST_SENSE			0x03
# define SCSI_CMD_INQUIRY			0x12
# define SCSI_CMD_MODE_SENSE_6			0x1a
# define SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL	0x1e
# define SCSI_CMD_READ_CAPACITY_10		0x25
# define SCSI_CMD_READ_10			0x28
# define SCSI_CMD_WRITE_10			0x2a

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
