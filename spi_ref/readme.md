The refinement of SPI controller model

### Description
Based on the spi controller model we defined in the folder /spi_model, we build an abstract spi controller model `spi_ref`. 

It removes most internal operations of SPI, to simplify the model. This model contains an update function `write_refregs`, a return function `read_refregs`, as well as 3 label functions for `TX`, `RX` and `XFER` respectively. 
Therefore, this model can update itself when driver issue write commands, or return a register's value and update its state for read commands, and more importandly, perform data transition with another spi device using `TX`, `RX` or `XFER` mode. 
The behaviors of the abstract model and the baisc one, from the driver angle, are the same basiclly. 

### Files
- `spi_refstateScript.sml`: define the datatypes of the `spi_ref` model, mainly remove some internal states of spi automatons.

- `write_refregsScript.sml`: define write-related functions that shows how the `spi_ref` updates itself according to the driver write commands.

- `read_refregsScript.sml`: define read-related functions for read commands.

- `spi_reflblScript.sml`: define 3 functions for TX, RX and XFER separately which are used for data transition between SPI deivces.

- `spi_ref_relScript.sml`: define the state transtion relation `spi_ref_tr` for this model, corresponding to `spi_tr`.

- `ref_RScript.sml`: define the refinement relation R for `spi_ref_state` and `spi_state`.

### Automaton
Compared to the basic model automatons, the figures below show the differences. In general, automatons are simplified without any tau transitions.

spi_ref init:

<img src="https://user-images.githubusercontent.com/34090109/94441085-9de08980-01a2-11eb-88ce-ff4a826562e3.png" width="90%"></img> 

spi_ref tx:

<img src="https://user-images.githubusercontent.com/34090109/94441583-3840cd00-01a3-11eb-9ce0-d01a84eedb66.png" width="90%"></img> 

spi_ref rx:

<img src="https://user-images.githubusercontent.com/34090109/94442517-5bb84780-01a4-11eb-8f27-b6285c02e27c.png" width="90%"></img> 

spi_ref xfer:

<img src="https://user-images.githubusercontent.com/34090109/94443932-0d0bad00-01a6-11eb-9c66-d6af23bcb6c1.png" width="90%"></img> 