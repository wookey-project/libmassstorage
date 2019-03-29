About the SCSI protocol
-----------------------

Principles
""""""""""

The SCSI stack has originally been defined for hard disk drives and is now used for various devices including USB thumb drives. For USB mass-storage device using SCI stack, commands are send by the initiator (the client) to the device (the server), through command blocks named *SCB*.
The server acknowledge each command and may, if the command requires it, send back or receive data on the read and write dedicated USB endpoints (usually, but not always, endpoint 1 and endpoint 2).


.. caution::
   The SCSI protocol is synchronous and request predefined command-response sequences defined in the SCSI standard

Limitations
"""""""""""

Developping a fully-efficient SCSI automaton is complex, as SCSI implementations of various OSes vary and sometimes require proprietary request (typically Microsoft requests a dedicated BULK level string identifier). Moreover, the standard is not made to be fully implemented, as it permits to handle various use cases, from USB mass-storage to fiber-channel and iSCSI protocols. This polymorphism make the SCSI standard complex to understand and to implement.


