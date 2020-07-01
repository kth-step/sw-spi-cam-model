This is the formal model of an SPI driver with a camera(TODO). The code follows Jonas NIC model's style.

### Files
- `board_memScript.sml` defines physical addresses of SPI registers and board RAM region. 
- `SPI_stateScript.sml` defines datatypes about SPI bus states and external environment, including Init, TX, RX, XFER processes, SPI registers, scheduler, etc.
- `SPI_initScript.sml` provides the SPI init automaton, mainly about how SPI performs reset operation.
- `SPI_txScript.sml` provides the SPI transmit automaton, that SPI transmits data to the slave through channel 0.
- `SPI_rxScript.sml` provides the SPI receive automaton, that SPI receives data from the slave through channel 0.
- `SPI_xferScript.sml` provides the SPI transfer(transmit and receive) automaton, since SPI supports full-duplex mode. In other words, this theory shows the SPI transmit and receive mode.
- `write_SPIregsScript.sml` describes that SPI updates its registers and states according to CPU-issued PA and Val.
- `read_SPIregsScript.sml` returns the value of corresponding SPI register, if CPU asked a PA in the SPI region.
- `SPI_schedulerScript.sml` determine which automaton should perform the next transition.
- `SPI_modelScript.sml` shows the SPI interfaces with CPU and environment. `spi_transition_write_regs_def` and `spi_transition_read_regs_def` show interactions of SPI and CPU, (how SPI worked if CPU wants to write/read a PA in SPI region). `spi_transition_autonomous_def` indicates SPI performed internal operations. `spi_transition_mem_reply_def` shows SPI operation when it got a byte from memory in the tx/xfer processes.

### Four automatons
In this SPI model, there are four automatons, init, tx, rx and xfer. Here are figures belong to each automaton.
<p align="center">
  <img src="https://user-images.githubusercontent.com/34090109/86120814-45cbb580-bad5-11ea-84cb-36041b6d40b1.jpg" width="90%"></img> 
  <img src="https://user-images.githubusercontent.com/34090109/86122242-c5f31a80-bad7-11ea-96b6-c1552642c7df.jpg" width="90%"></img>
  <img src="https://user-images.githubusercontent.com/34090109/86125294-b4604180-badc-11ea-812d-044f147b78ba.jpg" width="90%"></img>
  <img src="https://user-images.githubusercontent.com/34090109/86128711-05beff80-bae2-11ea-894b-c9afb47308be.jpg" width="90%"></img> 
</p>
