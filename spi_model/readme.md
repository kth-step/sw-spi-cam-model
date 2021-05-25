SPI hardware model

### Files
- `board_memScript.sml`: defines physical addresses of SPI registers and board RAM region.
- `SPI_stateScript.sml`: defines the state of SPI hardware. Basiclly, the SPI hardware model includes memory-mapped registers, shift register, an error flag, and a contral state that descibes the process of automatons.
- `SPI_update_regsScript.sml`: describes how SPI hardware updates its state and registers according to the driver-issued adress and value.
- `SPI_return_regsScript.sml`: describes how SPI hardware returns a value if the driver issues a read request to the memory-mapped registers.
- `SPI_tauScript.sml`: defines internal actions of SPI hardware.
- `SPI_data_trScript.sml`: shows the SPI hardware model's interface to transmit and receive data with three different modes, including TX, RX (both half-duplex) and XFER (full-duplex).
- `SPI_relationScript.sml`: defines the SPI hardware state transition relation.
- `weak_bisimulationScript.sml`: definitions for the weak bisimulation.
