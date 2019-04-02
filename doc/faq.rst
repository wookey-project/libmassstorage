LibMassstorage FAQ
------------------

When connected to my JTAG port, there is some regular freeze of the SCSI stack
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

Beware when keeping the JTAG port connected during the tests of the Wookey board. Incorrectly connected JTAG port of unstable connection may generate noise which can perturbate the high speed I/O ports such as USB High-Speed. Check if the problem still happen without the JTAG and the UART connected

There is some strange behavior of my USB tools on my host when I try to communicate with the Wookey
"""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""

If you are currently in a debug state of your Wookey device and if you have regulary reset/disconnect your device from your host, try to:

   1. change the USB port on which the device is connected
   2. reboot your host, as the USB host stack may have not correctly handle too much unstability on the USB ports

