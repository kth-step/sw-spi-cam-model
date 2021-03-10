SPI controller model

### Automaton
SPI init:

<img src="https://user-images.githubusercontent.com/34090109/101758876-29e32b80-3ad9-11eb-902c-1d0eaf0fd782.png" width="90%"></img>

SPI tx:

<img src="https://user-images.githubusercontent.com/34090109/103527392-8d673b80-4e82-11eb-90bc-113dc4803284.png" width="90%"></img> 

SPI rx:

<img src="https://user-images.githubusercontent.com/34090109/101759802-59defe80-3ada-11eb-9377-89db873a62b2.png" width="90%"></img> 

SPI xfer:

<img src="https://user-images.githubusercontent.com/34090109/101759968-8abf3380-3ada-11eb-9095-f98819d571e5.png" width="90%"></img> 

### Files
- `board_memScript.sml`: defines physical addresses of SPI registers and board RAM region.
- `SPI_stateScript.sml`: defines the datatypes for SPI controller. Basiclly, the SPI controller model includes SPI registers, an error flag, and a general state includes init, tx, rx, and xfer automatons.
- `SPI_update_regsScript.sml`: describes how SPI controller updates its states and regs according to driver-issued PA and Val.
- `SPI_return_regsScript.sml`: describes how SPI controller returns a value if the driver issues a read request to memory-mapped register.
- `SPI_tauScript.sml`: defines functions of SPI controller internal operation for init, tx, rx and xfer automatons.
- `SPI_data_trScript.sml`: shows the SPI hardware model's interface to transfer data with three different modes, including TX, RX (both half-duplex) and XFER (full-duplex).
- `SPI_relationScript.sml`: define SPI controller labeled state transition relation `spi_tr`.
