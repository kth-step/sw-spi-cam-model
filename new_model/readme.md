In order to fix the problem for SPI driver and controller, I create this folder for the updated model.

### Automaton
SPI tx:

<img src="https://user-images.githubusercontent.com/34090109/87311797-00b97180-c520-11ea-9830-dfbe0787af1a.jpg" width="90%"></img> 

### Update
2020.7.17: add other two automatons, `SPI_rxScript.sml` and `SPI_xferScript.sml`. Upload the scheduler and SPI model.

2020.7.13: update two new automatons, `SPI_initScript.sml` and `SPI_txScript.sml`, make changes in the `SPI_stateScript.sml` for new automatons.
- SPI_init: not changed, only reset operation by the hardware itself.
- SPI_tx: remove memory requests, since the SPI hardware does not issue mem_req. Insteadly, add states to handle data transmission. I mean the driver issues `write (TX0,data)` to SPI hardware, then the SPI controller has internel operations to transmit the data.

2020.7.10: update `SPI_stateScript.sml`, `write_SPIregsScript.sml` and `read_SPIregsScript.sml`.

- Rewrite the SPI controller state, include init, tx, rx, xfer states. Still need to figure out the internel states of tx, rx, xfer, e.g. remove memory request steps of these states.
- The write_SPI_regs provides the interface to update SPI state, spi -> spi' through write_SPI_regs(pa, v).
- read_SPI_regs: spi -> spi' through read_SPI_regs(pa).
- fix the mistake to clear TXS and RXS bit.

### Files
- `board_memScript.sml`: not changed, defines physical addresses of SPI registers and board RAM region.
- `SPI_stateScript.sml`: defines the datatypes for SPI controller and driver. Basiclly, the SPI controller model includes SPI registers and an error flag, the driver model includes 4 automatons(init tx rx xfer).
- `write_SPIregsScript.sml`: describes how SPI controller and driver updates their states according to driver-issued PA and Val.
- `read_SPIregsScript.sml`: describes how SPI controller returns a value if the driver or other parts issue a read request to SPI-mapped memory.
- `driver_initScript.sml`: defines a function of SPI driver to produce write request to SPI registers for initializing SPI controller, and a function of SPI controller to reset itself.

So far, the read/write_SPIregs are the interface for the controller and driver interactions. The driver's content would be how to issue the read and write requests to the controller, the controller only concerns how to update regs and error flag according to requests.

The next step I plan to re-define rx, tx and xfer processes belong to the driver following `driver_initScript.sml`'s way.

### Problem
I am not sure if the new model sloved the problem we talked last week. My idea is using write/read_SPITheory to indicate SPI controller's feedback for memory-requests, and then define the driver's model to issue these requests.
