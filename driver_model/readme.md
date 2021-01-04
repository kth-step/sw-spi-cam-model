This folder is the driver model.

### Files
- `driver_writeScript`: defines the `dr_write` function and related functions that issue write requests to the SPI controller according to the driver state.
- `driver_readScript`: defines the `dr_read` function and related functions that issue read requests to the SPI controller according to the driver state.
- `driver_checkScript`: defines the `dr_check` function and related funcions. It updates the driver state based on the reply from SPI hardware for previous read request.
- `driver_stateScript`: defines datatypes for the driver model.
- `driver_relationScript`: defines a relation for driver state to descibe the driver labeled state transitions.

### Driver state transition relation
driver_tr defines three rules:

1. (TAU_ENABLE dr) /\ (dr.dr_last_read_ad = SOME a) /\ (dr.dr_last_read_v = SOME v) ==> dr tau dr'

2. (WR_ENABLE dr) /\ (dr_write_address dr = SOME a) /\ (dr_write_value = SOME v) ==> dr (Write a v) dr'

3. (RD_ENABLE dr) /\ (dr_read dr.dr_last_read_ad = SOME a) ==> dr (Read a v) dr'

### Automaton
There are 4 automatons of the driver model, init, tx, rx and xfer. In the figures, Write means issue a write request to SPI controller, Read means issue a read request, and Check means check the reply for previous read request. rn represents the physical address of an SPI register, v is a value.

Driver init (initialize):

<img src="https://user-images.githubusercontent.com/34090109/101760907-ce666d00-3adb-11eb-8d46-f6161ce9bc4b.png" width="90%"></img> 

Driver tx (transmit):

<img src="https://user-images.githubusercontent.com/34090109/101761094-0968a080-3adc-11eb-8240-50512c591b16.png" width="90%"></img> 

Driver rx (receive):

<img src="https://user-images.githubusercontent.com/34090109/103527897-56ddf080-4e83-11eb-8be3-1d9fc6f27cbc.png" width="90%"></img>  

Driver xfer (transfer, full-duplex):

<img src="https://user-images.githubusercontent.com/34090109/101761457-74b27280-3adc-11eb-88b7-f2f8308e1f16.png" width="90%"></img> 
