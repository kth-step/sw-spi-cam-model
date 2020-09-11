This folder is the driver model.

### Files
- `driver_writeScript`: defines the `dr_write` function and its sub-functions that issue write requests to the SPI hardware according to the driver state.
- `driver_readScript`: defines the `dr_read` function and its sub-functions that issue read requests to the SPI hardware according to the driver state.
- `driver_checkScript`: defines the `dr_check` function and its sub-funcions. It updates the driver state based on the reply from SPI hardware for previous read request.
- `driver_stateScript`: defines datatypes for the driver model.
- `driver_relationScript`: defines a relation for driver state to descibe the driver state labeled transitions.

### Driver transition relation
In the `driver_relationScript`, I define a relation for the driver model. First, at any time, if the SPI controller replies a value v for register ad, the driver should check the reply and update itself, or the driver can ignore the reply and keep its state. Second, if the driver is in a state that can issue write request and the request is vaild (<> NONE), then the driver should issue the write request, finally the SPI controller will handle it. Third, the read request is similiar with the write one, but the request only has an address.

Moreover, I think the `local_tr` defined in the spi_model/SPI_relationScript.sml should be updated with the label `check word32 word32`. In details, the SPI controller returns a value v for register ad, then the driver check the reply.

`!(dr:driver_state) (spi:spi_state). (spi_tr spi (Return a v) spi') /\ (dr_tr dr (Check a v) dr') ==> local_tr (dr, spi) tau (dr', spi')`


### Automaton
There are 4 automatons of the driver model, init, tx, rx and xfer. In the figures, Write means issue a write request to SPI controller, Read means issue a read request, and Check means check the reply for previous read request. rn represents the physical address of an SPI register, v is a value.

Driver init (initialize):

<img src="https://user-images.githubusercontent.com/34090109/92883000-be71bb00-f410-11ea-817a-743cf42b092a.png" width="90%"></img> 

Driver tx (transmit):

<img src="https://user-images.githubusercontent.com/34090109/92888871-ff200300-f415-11ea-9b0e-7a77c34e3036.png" width="90%"></img> 

Driver rx (receive):

<img src="https://user-images.githubusercontent.com/34090109/92894805-304f0200-f41b-11ea-8ef6-24f7b1b77606.png" width="90%"></img> 

Driver xfer (transfer, full-duplex):

<img src="https://user-images.githubusercontent.com/34090109/92899641-46f75800-f41f-11ea-9192-f2709dc9d6c2.png" width="90%"></img> 
