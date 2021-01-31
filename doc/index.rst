.. _lib_usbmsc:

.. highlight:: c

The USBMSC stack
================

.. contents::

Overview
--------

The Libusbmsc project aim to implement a complete USB MSC (Mass storage class) stack for
various mass storage devices (USB keys, hard disk drives, etc.).
This stack is implemented using two layered substacks:

   * a BBB stack (Bulk-only device stack, used by most common USB storage devices (USB thumb drives, hard drives, CD, DVD and Blu-ray drives) to handle the transaction level
   * a SCSI stack, over the BBB stack, to handle the command set

Each substack handle its own state automaton. These two stacks are not visible from the usbmsc API, making the USB MSC manipulation easier to application level.

In this stack implementation, USB MSC commands are received in ISR threads and enqueued, to be asyncrhonously dequeued and executed in the task main thread.

The USB control stack is not a part of this library, and is handled by the libusbctrl stack.


.. note::
   The USB MSC stack is portable and does not rely on a specific driver implementation. It only request a given driver to support some USB oriented API, such as send_data, data_sent, ep_stall, etc.
   The USB driver abstraction is to be made by the driver itself or a proxy library if required.

The USB MSC stack has originally been defined for hard disk drives and is now used
for various devices including USB thumb drives. For USB mass-storage device
using SCSI stack, commands are send by the initiator (the client) to the device
(the server), through command blocks named *SCB*.

The server acknowledge each command and may, if the command requires it, send
back or receive data on the read and write dedicated USB endpoints (usually,
but not always, endpoint 1 and endpoint 2).

.. caution::
   The SCSI protocol is synchronous and request predefined command-response sequences defined in the SCSI standard

Limitations
"""""""""""

Developping a fully-efficient SCSI automaton is complex, as SCSI
implementations of various OSes vary and sometimes require proprietary request
(typically Microsoft requests a dedicated BULK level string identifier).
Moreover, the standard is not made to be fully implemented, as it permits to
handle various use cases, from USB mass-storage to fiber-channel and iSCSI
protocols. This polymorphism make the SCSI standard complex to understand and
to implement.



USB MSC API
-----------

The USB MSC Abstract the SCSI and BBB stacks using a high level API.

The USB MSC functional API
""""""""""""""""""""""""""

Initializing the stack
^^^^^^^^^^^^^^^^^^^^^^

Initialize the massstorage library is made through two main functions ::

   #include "libusbmsc.h"

   mbed_error_t usbmsc_declare(uint8_t*buf, uint16_t buflen);

   mbed_error_t usbmsc_initialize(uint32_t usbdci_handler);

   mbed_error_t usbmsc_initialize_automaton(void);

the declarative step is called before the task ends its initialization phase
using sys_init(INIT_DONE) syscall.
This syscall declare all the requested ressources that can only be declared
at initialization time. This include the USB device memory mapping (see EwoK documentation).

The task has to declare a buffer and a buffer size that will be used by the
MSC stack to hold data chunks during the READ and WRITE states.
The buffer size depend on the task constraints but **must be a multiple of
the endpoint USB URB size** (usually 512 bytes length).

.. note::
   Bigger the buffer is, faster the USB MSC stack is

The initialization step register the USB MSC against the USB control stack.
This permits to register endpoints and inform the control stack of the existence of
the USB MSC interface.

The automaton initialization step prepare the reception endpoint to be ready to receive
the first command.


Interacting with the storage backend
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Accessing the backend is not under the direct responsability of the USB MSC stack.
Depending on the way the device is implemented, backend storage can be localy accessed,
handled by another task, or remotely accessed through a local proxy, making the local USB
MSC task an abstraction of a backend storage area.

Although, the stack need to request backend write and/or read access in
WRITE and READ states.

To allow flexibility in how the storage backend is handled, the task has to
decrlare the following functions::

   mbed_error_t usbmsc_storage_backend_write(uint32_t sector_addr, uint32_t num_sectors);
   mbed_error_t usbmsc_storage_backend_read(uint32_t sector_addr, uint32_t num_sectors);
   mbed_error_t usbmsc_storage_backend_capacity(uint32_t *numblocks, uint32_t *blocksize);

The *usbmsc_storage_backend_write()* function is called by the USB MSC stack when a
data chunk has been received. This function is then responsible of the
communication with the storage manager (SDIO, EMMC or any storage backend), and
should return MBED_ERROR_NONE if the storage has acknowledge correctly the chunk write. The
data chunk is at most of buflen size, but the associated WRITE command may
request bigger write. The USB MSC stack is responsible of the write split.

The *usbmsc_storage_backend_read()* function is called by the USB MSC stack when the
host is requesting data from the device. Again, the READ command may
request more than the buffer capacity. The USB MSC stack is also responsible of
the data requests split.

The *scsi_storage_backend_capacity()* is called when the host is
requesting the storage backend capacity. This is usually the consequence of a
MODE SENSE request from the host, to which the USB MSC stack return various
informations about the device and the SCSI stack itself.

.. danger::
   These functions **must** be defined by the application or the link step will
   fail to find these three symbols at link time

.. caution::
   All addresses and sizes are in SCSI sectors unit. This information is generally
   shared with the storage manager, which also manipulate sectors. Althrough,
   sector size may be translated by the storage manager if needed (e.g. from 512
   to 4096 bytes length). OSes usually support from 512 to 4096 bytes sectors size

Backend access, in the USB MSC stack, is synchronous and not made for asynchronous
read or write.

Executing the USB MSC automaton
"""""""""""""""""""""""""""""""

The USB MSC automaton is executed in main thread using the following function ::

   #include "libusbmsc.h"
   void usbmsc_exec_automaton(void);

A basic usage of the automaton would be ::

   while (1) {
       usbmsc_exec_automaton();
   }


Handling reset
""""""""""""""

When a USB reset is received (connecting a device to/from a virtual machine, communication error and so on),
the USB MSC stack has to reinitialize itself to resart properly.

The reset information is received by the USB MSC stack and is transmitted to the task using the usbmsc_reset_stack() ::

   void usbmsc_reset_stack(void);

.. danger::
   Again, this function is to be declared by the upper stack to handle reset properly. A basic use of this function is to set a reset flag

At reset time, the USB MSC stack needs to be reinitialize, in order to clear potential command that are being executed.
Current offsets are cleared. The buffer is keeped.

A basic full usage of USB MSC stack with reset support is the following  ::

   #include "libusbmsc.h"

   static volatile bool reset_requested = false;
   static volatile bool conf_set = false;

   // USB MSC trigger for reset
   void usbmsc_reset_stack(void) {
       reset_requested = true;
   }

   // USBCtrl trigger for ConfigurationSet (see usbctrl doc)
   void usbctrl_configuration_set(void)
   {
       conf_set = true;
   }

   #define USB_BUF_SIZE 4096
   uint8_t usb_buf[USB_BUF_SIZE];

   int main(void) {
       mbed_error_t errcode;
       uint32_t usbxdci_hander;
       [...]
       errcode = usbctrl_declare(USB_OTG_HS_ID, &usbxdci_handler);
       [...]
       errcode = usbctrl_initialize(usbxdci_handler);
       [...]
       errcode = usbmsc_declare(&(usb_buf[0]), USB_BUF_SIZE);
       [...]

       ret = sys_init(INIT_DONE);

       usbmsc_initialize(usbxdci_handler);

       usbctrl_start_device(usbxdci_handler);

       do {
           reset_requested = false;
           /* in case of RESET, reinit context to empty values */
           usbmsc_reinit();

            while (!conf_set) {
               /* wait for SetConfiguration */
               ;
           }
           printf("Set configuration received\n");
           /* execute SCSI automaton */
           usbmsc_initialize_automaton();
           while (!reset_requested) {
               usbmsc_exec_automaton();
           }
           /* reset received! go back to default */
           conf_set = false;
       } while (1);
   }



Supported SCSI commands
"""""""""""""""""""""""

The SCSI standard is huge and the requested supported commands depend on the
SCSI device type, the host Operating System SCSI stack version and some
inter-commands dependencies.

Today, the USB MSC SCSI substack supports the following commands:

   * FORMAT UNIT
   * INQUIRY
   * MODE SELECT(6)
   * MODE SELECT(10)
   * MODE SENSE(6)
   * MODE SENSE(10)
   * PREVENT ALLOW MEDIUM REMOVAL
   * READ FORMAT CAPACITIES
   * READ(6)
   * READ(10)
   * READ CAPACITY(10)
   * READ CAPACITY(16)
   * READ FORMAT CAPACITIES
   * REPORT LUNS
   * START STOP UNIT
   * SYNCHONIZE CACHE(10)
   * TEST UNIT READY
   * VERIFY(10)
   * WRITE(6)
   * WRITE(10)

Debugging the stack
"""""""""""""""""""

Both SCSI and BBB stack can be debugged easily using the USBMSC menu of the library
in the configuration menu. There is three levels of debug:

   * 0: no debug at all. Production mode
   * 1: SCSI and BBB commands sequence. All SCSI command are printed on the serial interface
   * 2: SCSI and BBB commands dump and behavior: complex commands (inquiry, etc.) are dumped
        on the serial interface. Triggers (data sent, data available) events are
        printed. amount of data sent or received are also printed.

The debugging is functional only if the kernel serial console is activated.

