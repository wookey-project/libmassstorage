/** @file usb_control_mass_storage.c
 *
 */
#include "autoconf.h"
#include "api/print.h"
#include "api/regutils.h"
#include "api/usb.h"
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
		usb_driver_send(&max_lun, sizeof(max_lun), USB_FS_DXEPCTL_EP0);
		usb_driver_read(NULL, 0, USB_FS_DXEPCTL_EP0); //FIXME why this here ?
#endif
#ifdef CONFIG_USR_DRV_USB_HS
		usb_driver_send(&max_lun, sizeof(max_lun), USB_HS_DXEPCTL_EP0);
		usb_driver_read(NULL, 0, USB_HS_DXEPCTL_EP0); //FIXME why this here ?
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
    	};

	usb_ctrl_init(usbmass_usb_ctrl_callbacks, usbmass_device_desc , usbmass_configuration_desc );
}
