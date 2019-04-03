#ifndef SCSI_H
# define SCSI_H


/**
 * SCSI stack implementation
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
mbed_error_t scsi_storage_backend_read(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief Write data to the storage backend
 *
 * \param sector_addr SCSI sector address where the data must be written
 * \param num_sectors number of sectors to write
 *
 * \return 0 on success
 */
mbed_error_t scsi_storage_backend_write(uint32_t sector_addr, uint32_t num_sectors);

/*
 * \brief get back the backend storage capacity
 *
 * \param numblock number of SCSI blocks
 * \param blocksize size of one SCSI block
 *
 * \return 0 on success
 */
mbed_error_t scsi_storage_backend_capacity(uint32_t *numblocks, uint32_t *blocksize);


/***********************************************************
 * libSCSI API
 ***********************************************************/

uint8_t scsi_early_init(uint8_t*buf, uint16_t buflen);

mbed_error_t scsi_init(void);

void scsi_send_data(void *data, uint32_t size);

void scsi_get_data(void *buffer, uint32_t size);

int scsi_is_ready_for_data(void);

void scsi_send_status(void);

void scsi_exec_automaton(void);

#endif /* SCSI_H */
