/** @file usb_control_mass_storage.c
 *
 */
#include "autoconf.h"
#include "api/print.h"
#include "api/regutils.h"
#include "usb.h"
#include "usb_control_mass_storage.h"
#include "usbmass_desc.h"


static void mass_storage_reset(void)
{
    	printf("Bulk-Only Mass Storage Reset\n");
}


/**
 * \brief Class request handling for bulk mode.
 *
 * @param packet Setup packet
 */
void mass_storage_class_rqst_handler(struct usb_setup_packet *packet)
{
	uint8_t max_lun = 0;
	switch (packet->bRequest) {
	case USB_RQST_GET_MAX_LUN:
#ifdef CONFIG_USR_DRV_USB_FS
		usb_driver_setup_send(&max_lun, sizeof(max_lun), USB_FS_DXEPCTL_EP0);
		usb_driver_setup_read(NULL, 0, USB_FS_DXEPCTL_EP0); //FIXME why this here ?
#endif
#ifdef CONFIG_USR_DRV_USB_HS
		usb_driver_setup_send(&max_lun, sizeof(max_lun), USB_HS_DXEPCTL_EP0);
		usb_driver_setup_read(NULL, 0, USB_HS_DXEPCTL_EP0); //FIXME why this here ?
#endif

		break;
	case USB_RQST_MS_RESET:
        	mass_storage_reset(); // FIXME We must use a callback function
		break;
		// FIXME: break here or not????
	default:
		/* TODO: send error status */
		printf("Unhandled class request (%x)\n", packet->bRequest);
	}
}


static void mass_storage_mft_string_desc_rqst_handler(uint16_t wLength){
    uint32_t i;
    uint32_t len;
     printf("MFT String, wLength:\n", wLength);
    usb_string_descriptor_t string_desc;

    if ( wLength == 0 ){
        usb_driver_setup_send_status(0);
        usb_driver_setup_read_status();
        return;
    }

    string_desc.bDescriptorType = USB_DESC_STRING;
    len = MSFT100_SIG_SIZE + 4;
    string_desc.bLength = 0x12;
    string_desc.bDescriptorType = 0x03;
    for (i = 0; i < MSFT100_SIG_SIZE; i++)
        string_desc.wString[i] = MSFT100_SIG[i];
    string_desc.wString[MSFT100_SIG_SIZE] = 0x05;
    string_desc.wString[MSFT100_SIG_SIZE + 1] = 0x00;

    if ( wLength > string_desc.bLength){
        usb_driver_setup_send((uint8_t *)&string_desc, string_desc.bLength, EP0);
    }else{
        usb_driver_setup_send((uint8_t *)&string_desc, wLength, EP0);
    }
    usb_driver_setup_read_status();
}

/**
 * \brief Set callback for class_rqst in usb_control
 */
void mass_storage_init(void)
{
	usb_ctrl_callbacks_t usbmass_usb_ctrl_callbacks = {
        	.class_rqst_handler             = mass_storage_class_rqst_handler,
        	.vendor_rqst_handler            = NULL,
        	.set_configuration_rqst_handler = NULL,
        	.set_interface_rqst_handler     = NULL,
        	.functional_rqst_handler        = NULL,
            .mft_string_rqst_handler        = mass_storage_mft_string_desc_rqst_handler,

    	};

	usb_ctrl_init(usbmass_usb_ctrl_callbacks, usbmass_device_desc , usbmass_configuration_desc );
}
