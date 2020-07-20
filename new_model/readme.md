In order to fix the problem for SPI driver and controller, I create this folder for the updated model.

### Automaton
SPI tx:

<img src="https://user-images.githubusercontent.com/34090109/87311797-00b97180-c520-11ea-9830-dfbe0787af1a.jpg" width="90%"></img> 

SPI rx:

<img src="https://user-images.githubusercontent.com/34090109/87920713-ddd81180-ca79-11ea-8db6-773230b96e7d.jpg" width="90%"></img>

SPI xfer:

<img src="https://user-images.githubusercontent.com/34090109/87921914-89359600-ca7b-11ea-8a15-22db875892c8.jpg" width="90%"></img> 

SPI init:

<img src="https://user-images.githubusercontent.com/34090109/87917189-dc581a80-ca74-11ea-9c14-25bcbcedfb50.jpg" width="90%"></img> 


### Update
2020.7.20: upload the new version of SPI controller model and update the `Readme` text.


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

The next step I plan to define the SPI slave in the environment and prove basic properties.

### Problem
