This folder is the driver model.

### Files
- `driver_writeScript`: defines the `dr_write` function and its sub-functions that issue write requests to the SPI hardware according to the driver state.
- `driver_readScript`: defines the `dr_read` function and its sub-functions that issue read requests to the SPI hardware according to the driver state.
- `driver_checkScript`: defines the `dr_check` function and its sub-funcions. It updates the driver state based on the reply from SPI hardware for previous read request.
- `driver_stateScript`: defines datatypes for the driver model.
- `driver_relationScript`: defines a relation for driver state to descibe the driver state labeled transitions.

### Automaton
There are 4 automatons of the driver model, init, tx, rx and xfer. 

Driver init (initialize):

<img src="https://user-images.githubusercontent.com/34090109/92883000-be71bb00-f410-11ea-817a-743cf42b092a.png" width="90%"></img> 

Driver tx (transmit):

<img src="https://user-images.githubusercontent.com/34090109/92888871-ff200300-f415-11ea-9b0e-7a77c34e3036.png" width="90%"></img> 

Driver rx (receive):

<img src="https://user-images.githubusercontent.com/34090109/92894805-304f0200-f41b-11ea-8ef6-24f7b1b77606.png" width="90%"></img> 

Driver xfer (transfer, full-duplex):

<img src="https://user-images.githubusercontent.com/34090109/92899641-46f75800-f41f-11ea-9192-f2709dc9d6c2.png" width="90%"></img> 
