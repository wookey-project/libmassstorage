#ifndef USB_BBB_H
# define USB_BBB_H

# include "api/regutils.h"

/**
 * usb_bbb_init - Initialize the bulk only layer
 * @cmd_received: callback called when a command is received. Parameters are the
 * command block and its size.
 * @data_received: callback called when data is received. The parameter is the
 * size of received data.
 * @data_sent: callback called when data has been sent
 */
void usb_bbb_init(void);

void usb_bbb_early_init(void (*cmd_received)(uint8_t cdb[],
                        uint8_t cdb_len),
		                void (*data_received)(uint32_t),
		                void (*data_sent)(void));


enum csw_status {
	CSW_STATUS_SUCCESS = 0,
	CSW_STATUS_FAILED = 1,
	CSW_STATUS_ERROR = 2 /* host should send reset */
};
/**
 * usb_bbb_send_csw - Send the status of the command
 * @src: address of the data to send. The buffer's size must be at list @size.
 * @data_residue: number of bytes not sent nor received.
 */
void usb_bbb_send_csw(enum csw_status status, uint32_t data_residue);

/**
 * usb_bbb_send - Send data throw USB layer
 * @src: address of the data to send. The buffer's size must be at least @size.
 * @size: number of bytes to send.
 * @ep: endpoint on which send data.
 */
void usb_bbb_send(const uint8_t *src, uint32_t size, uint8_t ep);

/**
 * usb_bbb_read - Read data from USB layer
 * @dst: buffer in which read data will be written.
 * @size: number of bytes to read.
 * @ep: endpoint on which read data.
 */
void usb_bbb_read(void *dst, uint32_t size, uint8_t ep);

#endif /* USB_BBB_H */
