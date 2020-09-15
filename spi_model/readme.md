In order to fix the problem for SPI driver and controller, I create this folder for the updated model.

### Update
2020.9.15: 

Update readme figures.

### Automaton
SPI init:

<img src="https://user-images.githubusercontent.com/34090109/93185806-2c362380-f73e-11ea-8ecb-d6d09b33f6fd.png" width="90%"></img> 

SPI tx:

<img src="https://user-images.githubusercontent.com/34090109/93186028-6d2e3800-f73e-11ea-9722-550d3ca162e4.png" width="90%"></img> 

SPI rx:

<img src="https://user-images.githubusercontent.com/34090109/93186137-90f17e00-f73e-11ea-9891-83919814bd6a.png" width="90%"></img>

SPI xfer:

<img src="https://user-images.githubusercontent.com/34090109/93186238-aebee300-f73e-11ea-82ac-b177c9a83730.png" width="90%"></img> 

### Files
- `board_memScript.sml`: defines physical addresses of SPI registers and board RAM region.
- `SPI_stateScript.sml`: defines the datatypes for SPI controller, SPI driver(TODO) and the environment. Basiclly, the SPI controller model includes SPI registers, an error flag, and automaton's states includes init, tx, rx, and xfer.
- `write_SPIregsScript.sml`: describes how SPI controller and driver updates their states according to driver-issued PA and Val.
- `read_SPIregsScript.sml`: describes how SPI controller returns a value if the driver or other parts issue a read request to SPI-mapped memory.
- `SPI_initScript.sml`: defines functions of SPI controller internal operation for initializing SPI bus.
- `SPI_txScript.sml`: define functions of SPI controller for transmit automaton.
- `SPI_rxScript.sml`: define functions of SPI controller for receive automaton.
- `SPI_xferScript.sml`: define functions of SPI controller for transfer automaton, full-duplex.
- `SPI_schedulerScript.sml`: indicates SPI hardware internal excution steps.
- `SPI_modelScript.sml`: shows the SPI hardware model's interface with CPU(issues read/write request to SPI) and its internal operations(according to the scheduler).
- `SPI_relationScript.sml`: define SPI controller state labeled transition relation `spi_tr`.
