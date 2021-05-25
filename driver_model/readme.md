SPI driver model

### Files
- `driver_stateScript`: defines the state of the driver model, including error flag, data buffers, index, control state, last_read_v, etc.
- `driver_writeScript`: defines the `dr_write` function and related functions that issue write requests to the SPI hardware.
- `driver_readScript`: defines the `dr_read` function and related functions that issue read requests to the SPI hardware.
- `driver_checkScript`: defines the check funcions which are the internal actions of the driver.
- `driver_callScript`: defines the interface that the driver model handle function calls and reply data.
- `driver_relationScript`: defines a relation for the driver model to descibe its state transitions.
