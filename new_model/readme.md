In order to fix the problem for SPI driver and controller, I create this folder for the updated model.

- `board_memScript.sml`: not changed, defines physical addresses of SPI registers and board RAM region.
- `SPI_stateScript.sml`: defines the datatypes for SPI controller and driver. Basiclly, the SPI controller model includes SPI registers and an error flag, the driver model includes 4 automatons(init tx rx xfer).
- `write_SPIregsScript.sml`: describes how SPI controller and driver updates their states according to driver-issued PA and Val.
- `read_SPIregsScript.sml`: describes how SPI controller returns a value if the driver or other parts issue a read request to SPI-mapped memory.

So far, the read/write_SPIregs are the interface for the controller and driver interactions. The driver's content would be how to issue the read and write requests to the controller, the controller only concerns how to update regs and error flag according to requests.

The next step I plan to re-define init, rx, tx and xfer processes belong to the driver. For example, the `driver_initScript.sml` contains functions to produce read and write reqs to SPI for initializing SPI controller.
