The refinement of SPI controller model

### Description
Based on the spi controller model we defined in folder spi_model, we build an abstract spi controller model `spi_ref`. 

It removes most internal operations of SPI, to simplify the model. This model contains an update function `write_refregs`, a return function `read_refregs`, as well as 3 label functions for `TX`, `RX` and `XFER` respectively. 
Therefore, this model can update itself when driver issue write commands, or return a register's value and update its state for read commands, and more importandly, perform data transition with another spi device using `TX`, `RX` or `XFER` mode. 
The behaviors of the abstract model and the baisc one, from the driver angle, are the same basiclly. 

### Files
- `spi_refstateScript.sml`: define the datatypes of the `spi_ref` model, mainly remove some internal states of spi automatons.

- `write_refregsScript.sml`: define write-related functions, that shows how the `spi_ref` update itself according to the driver write commands.

- `read_refregsScript.sml`: define read-related functions for read commands.

- `spi_reflblScript.sml`: define 3 functions for TX, RX and XFER separately which are used for data transition between SPI deivces.

- `spi_ref_relScript.sml`: define the state transtion relation `spi_ref_tr` for this model, corresponding to `spi_tr`.

- `ref_RScript.sml`: define the refinement relation R for `spi_ref_state` and `spi_state`.

### Automaton
Figures to add
