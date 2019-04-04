#include "api/stdio.h"
#include "api/nostd.h"
#include "api/regutils.h"
#include "usb.h"
#include "usb_bbb.h"


#define BBB_DEBUG 0

enum bbb_state {
	READY,
	CMD,
	DATA,
	STATUS,
};

static void (*callback_cmd_received)(uint8_t cdb[], uint8_t cdb_len);
static void (*callback_data_received)(uint32_t size);
static void (*callback_data_sent)(void);


static volatile enum bbb_state bbb_state;
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
#if BBB_DEBUG
	printf("[USB BBB] %s: Reading a command\n",  __func__ );
#endif
	bbb_state = READY;
	usb_driver_setup_read(&cbw, sizeof(cbw), 1);
}

static void usb_bbb_cmd_received(uint32_t size)
{
	if (size != sizeof(struct scsi_cbw) || cbw.sig != USB_BBB_CBW_SIG) {
		aprintf("[USB BBB] %s: CBW not valid\n", __func__ );
		return;
	}
	if (cbw.flags.reserved || cbw.lun.reserved || cbw.cdb_len.reserved || cbw.lun.lun) {
		/* XXX: the only valid LUN for our device is 0 */
		/* TODO: check that cbw.cdb_len and cbw.cdb are in accordance
		 * with InferfaceSubClass
		 */
#if BBB_DEBUG
		aprintf("[USB BBB] %s: CBW not meaningful\n", __func__ );
#endif
		return;
	}
	current_tag = cbw.tag;
	bbb_state = CMD;
#if BBB_DEBUG
	aprintf("[USB BBB] %s: Command received\n", __func__ );
#endif
	callback_cmd_received(cbw.cdb, cbw.cdb_len.cdb_len);
}

static void usb_bbb_data_received(uint32_t size)
{
#if BBB_DEBUG
    aprintf("[USB BBB] %s bbb_state: %x ... \n", __func__, bbb_state);
#endif
    switch(bbb_state) {
        case READY:
		    usb_bbb_cmd_received(size);
            break;
        case STATUS:
		    bbb_state = READY;
            break;
        case DATA:
		    callback_data_received(size);
            break;
        default:
		    aprintf("[USB BBB] %s: ERROR usb_bbb_data_received ... \n", __func__ );
	}
}

static void usb_bbb_data_sent(void)
{
	switch (bbb_state) {
	case STATUS:
#if BBB_DEBUG
		aprintf("[USB BBB] %s: data sent while in STATUS state\n", __func__ );
#endif
		read_next_cmd();
		break;
	case DATA:
#if BBB_DEBUG
		aprintf("[USB BBB] %s: data sent while in DATA state\n", __func__ );
#endif
		callback_data_sent();
		break;
	case READY:
#if BBB_DEBUG
		aprintf("[USB BBB] %s: data sent while in READY state\n", __func__ );
#endif
		break;
	case CMD:
#if BBB_DEBUG
		aprintf("[USB BBB] %s: data sent while in CMD state\n", __func__ );
#endif
		break;
	default:
		aprintf("[USB BBB] %s: Unknown bbb_state\n", __func__ );
	}
}

void usb_bbb_early_init(void (*cmd_received)(uint8_t cdb[], uint8_t cdb_len),
		  void (*data_received)(uint32_t),
		  void (*data_sent)(void))
{
#if BBB_DEBUG
		printf("[USB BBB] %s\n", __func__ );
#endif
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
#if BBB_DEBUG
	aprintf("[USB BBB] %s: Sending CSW (%x, %x, %x, %x)\n", __func__, csw.sig, csw.tag, csw.data_residue, csw.status);
#endif
	usb_driver_setup_send((uint8_t *)&csw, sizeof(csw), 2);
}

void usb_bbb_send(const uint8_t *src, uint32_t size, uint8_t ep)
{
#if BBB_DEBUG
		aprintf("[USB BBB] %s\n", __func__ );
#endif
	bbb_state = DATA;
	usb_driver_setup_send(src, size, ep);
}

void usb_bbb_read(void *dst, uint32_t size, uint8_t ep)
{
#if BBB_DEBUG
		aprintf("[USB BBB] %s\n", __func__ );
#endif
	bbb_state = DATA;
	usb_driver_setup_read(dst, size, ep);
}
