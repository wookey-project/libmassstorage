#ifndef SCSI_CMD_H_
# define SCSI_CMD_H_


/* SCSI commands */
typedef enum {
    SCSI_CMD_FORMAT_UNIT                   = 0x04, // Mandatory
    SCSI_CMD_INQUIRY			            = 0x12, // Mandatory
    SCSI_CMD_MODE_SELECT_6                 = 0x15,
    SCSI_CMD_MODE_SELECT_10                = 0x55,
    SCSI_CMD_MODE_SENSE_10	                = 0x5a, // Requiered for some bootable devices
    SCSI_CMD_MODE_SENSE_6                  = 0x1a, // Requiered for some bootable devices
    SCSI_CMD_PREVENT_ALLOW_MEDIUM_REMOVAL	= 0x1e,
    SCSI_CMD_READ_6  			            = 0x08, // Mandatory for olders
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
    SCSI_CMD_WRITE_6 			            = 0x0a, // Mandatory for olders
    SCSI_CMD_WRITE_10			            = 0x2a, // Mandatory
    SCSI_CMD_READ_CAPACITY_16		        = 0x9e,
} scsi_operation_code_t;

#endif/*!SCSI_CMD_H_*/
