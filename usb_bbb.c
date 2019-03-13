#include "api/stdio.h"
#include "api/nostd.h"
#include "api/regutils.h"
#include "usb.h"
#include "usb_bbb.h"

enum bbb_state {
	READY,
	CMD,
	DATA,
	STATUS,
};

static void (*callback_cmd_received)(uint8_t cdb[], uint8_t cdb_len);
static void (*callback_data_received)(uint32_t size);
static void (*callback_data_sent)(void);


static enum bbb_state bbb_state;
uint32_t current_tag;



/* Command Block Wrapper */
struct __packed scsi_cbw {
	uint32_t sig;
	uint32_t tag;
	uint32_t transfer_len;
	struct {
		uint8_t reserved:7;
		uint8_t direction:1;
	} flags;
	struct {
		uint8_t lun:4;
		uint8_t reserved:4;
	} lun;
	struct {
		uint8_t cdb_len:5;
		uint8_t reserved:3;
	} cdb_len;
	uint8_t cdb[16]; // FIXME We must handle CDB6 CDB10 CDB12 CDB16 ?
};
static struct scsi_cbw cbw;
# define USB_BBB_CBW_SIG		0x43425355 /* "USBC" */

static void read_next_cmd(void)
{
	//printf("[USB BBB] Reading a command\n");
	bbb_state = READY;
	usb_driver_setup_read(&cbw, sizeof(cbw), 1);
}

static void usb_bbb_cmd_received(uint32_t size)
{
	if (size != sizeof(struct scsi_cbw) || cbw.sig != USB_BBB_CBW_SIG) {
		printf("[USB BBB] CBW not valid\n");
		return;
	}
	if (cbw.flags.reserved || cbw.lun.reserved || cbw.cdb_len.reserved || cbw.lun.lun) {
		/* XXX: the only valid LUN for our device is 0 */
		/* TODO: check that cbw.cdb_len and cbw.cdb are in accordance
		 * with InferfaceSubClass
		 */
		printf("[USB BBB] CBW not meaningful\n");
		return;
	}
	current_tag = cbw.tag;
	bbb_state = CMD;

	//printf("[USB BBB] Command received\n");
	callback_cmd_received(cbw.cdb, cbw.cdb_len.cdb_len);
}

static void usb_bbb_data_received(uint32_t size)
{
	if (bbb_state == READY){
		usb_bbb_cmd_received(size);
	}
	else if (bbb_state == STATUS){
		bbb_state = READY;
	}
	else if (bbb_state == DATA){
		callback_data_received(size);
	}
}

static void usb_bbb_data_sent(void)
{
	switch (bbb_state) {
	case STATUS:
		read_next_cmd();
		break;
	case DATA:
		callback_data_sent();
		break;
	case READY:
		printf("[USB BBB] data sent while in CMD state\n");
		break;
	case CMD:
		printf("[USB BBB] data sent while in CMD state\n");
		break;
	default:
		printf("[USB BBB] Unknown bbb_state\n");
	}
}

void usb_bbb_early_init(void (*cmd_received)(uint8_t cdb[], uint8_t cdb_len),
		  void (*data_received)(uint32_t),
		  void (*data_sent)(void))
{
	callback_cmd_received = cmd_received;
	callback_data_received = data_received;
	callback_data_sent = data_sent;

	usb_driver_early_init(usb_bbb_data_received, usb_bbb_data_sent);

}

void usb_bbb_init(void)
{
	usb_driver_init();

	bbb_state = READY;
	/* Read first command */
	read_next_cmd();
}

/* Command Status Wrapper */
struct __packed scsi_csw {
	uint32_t sig;
	uint32_t tag;
	uint32_t data_residue;
	uint8_t status;
};
# define USB_BBB_CSW_SIG			0x53425355 /* "USBS" */

void usb_bbb_send_csw(enum csw_status status, uint32_t data_residue)
{
	struct scsi_csw csw = {
		.sig = USB_BBB_CSW_SIG,
		.tag = current_tag,
		.data_residue = data_residue,
		.status = status
	};

	bbb_state = STATUS;

	//printf("[USB BBB] Sending CSW (%x, %x, %x, %x)\n", csw.sig, csw.tag, csw.data_residue, csw.status);
	usb_driver_setup_send((uint8_t *)&csw, sizeof(csw), 2);
}

void usb_bbb_send(const uint8_t *src, uint32_t size, uint8_t ep)
{
	bbb_state = DATA;
	usb_driver_setup_send(src, size, ep);
}

void usb_bbb_read(void *dst, uint32_t size, uint8_t ep)
{
	bbb_state = DATA;
	usb_driver_setup_read(dst, size, ep);
}
