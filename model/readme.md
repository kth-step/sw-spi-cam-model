This is the formal model of an SPI driver with a camera.The code follows Jonas NIC model's style.

### Files
- `board_memScript.sml` defines physical addresses of SPI registers and board RAM region. 
- `SPI_stateScript.sml` defines datatypes about SPI bus states and externel environment, including Init, TX, RX, XFER processes,SPI registers, shceduler, etc.
- `SPI_initScript.sml` provides the SPI init automaton, mainly about how SPI performs reset operation.
- `SPI_txScript.sml` provides the SPI transmit automaton, that SPI transmits data to the slave through channel 0.
- `SPI_rxScript.sml` provides the SPI receive automaton, that SPI receives data from the slave through channel 0.
- `SPI_xferScript.sml` provides the SPI transfer(transmit and receive) automaton, since SPI supports full-dulplex mode. In other words, this theory shows the SPI transmit and receive mode.
- `write_SPIregsScript.sml` describes that SPI updates its registers and states according CPU-issued PA and Val.
- `read_SPIregsScript.sml` returns the value of corresponding SPI register, if CPU asked a PA in SPI region.
- `SPI_schedulerScript.sml` determines whcih automaton should perform the next transition.
- `SPI_modelScript.sml` shows the SPI interfaces with CPU and environment. `spi_transition_write_regs_def` and `spi_transition_read_regs_def` shows interactions of SPI and CPU, (how SPI worked if CPU wants to write/read a PA in SPI region).
