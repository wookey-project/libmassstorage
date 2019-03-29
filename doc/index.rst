Welcome to the libMassStorage project documentation!
====================================================

The LibMassStorage project aim to implement a complete SCSI stack for mass storage
devices.
This SCSI stack is implemented as a state automaton, executing SCSI commands in the
main thread, handling and enqueuing command events in ISR threads.

This stack does not aim to implement the USB control stack or the USB driver, and request
these two components to exists. By now, this stack implement the BULK layer implementation
of the USB stack.

.. info::
   The BULK support is to be moved as an independent libbulk library in a near future

The current implementation of libMassStorage is compatible with the
Wookey STM32F439 driver API, and should be easily portable with other drivers.

.. toctree::
   :caption: Table of Contents
   :name: mastertoc
   :maxdepth: 2

   About the SCSI protocol <about>
   The SCSI API <api>
   FAQ <faq>

