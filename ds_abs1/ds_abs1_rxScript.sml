open HolKernel bossLib boolLib Parse;
open listTheory ds_abs1_stateTheory;

val _ = new_theory "ds_abs1_rx";

(* SPI_ABS1_RX_ENABLE: ds_abs1's state is permitted to perform SPI controller related internal rx operations. *)
val SPI_ABS1_RX_ENABLE_def = Define `
SPI_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_idle) \/
(ds_abs1.state = abs1_rx_update) \/
(ds_abs1.state = abs1_rx_next))`

(* DRIVER_ABS1_RX_ENABLE: ds_abs1's state is permitted to perform SPI driver related internal rx operations. *)
val DRIVER_ABS1_RX_ENABLE_def = Define `
DRIVER_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_ready) \/
(ds_abs1.state = abs1_rx_fetch_data) \/
(ds_abs1.state = abs1_rx_next) \/
(ds_abs1.state = abs1_rx_next_ready))`

(* COMB_ABS1_RX_ENABLE: ds_abs1's state is permitted to perform other internal rx operations. *)
val COMB_ABS1_RX_ENABLE_def = Define `
COMB_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_read) \/
(ds_abs1.state = abs1_rx_reset))`

(* ABS1_RX_LBL_ENABLE: ds_abs1's state is permitted to perform RX label operations. *)
val ABS1_RX_LBL_ENABLE_def = Define `
ABS1_RX_LBL_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_receive) \/
(ds_abs1.state = abs1_rx_fetch_data))`

(* SPI controller related internal rx functions *)
val spi_abs1_rx_idle_op_def = Define `
spi_abs1_rx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_receive`

val spi_abs1_rx_update_op_def = Define `
spi_abs1_rx_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_ready`

val spi_abs1_rx_next_op_def = Define `
spi_abs1_rx_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_next_ready`

val spi_abs1_rx_operations_def = Define `
spi_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_rx_idle) then
(spi_abs1_rx_idle_op ds_abs1)
else if (ds_abs1.state = abs1_rx_update) then
(spi_abs1_rx_update_op ds_abs1)
else if (ds_abs1.state = abs1_rx_next) then
(spi_abs1_rx_next_op ds_abs1)
else ds_abs1 with err := T`

(* SPI driver related internal rx functions *)
val driver_abs1_rx_ready_op_def = Define `
driver_abs1_rx_ready_op (ds_abs1:ds_abs1_state) =
ds_abs1 with 
state := if ds_abs1.ds_abs1_rx.rx_left_length > 0 then abs1_rx_read else abs1_rx_reset`

val driver_abs1_rx_fetch_data_op_def = Define `
driver_abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG]; 
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := abs1_rx_receive |>`

val driver_abs1_rx_next_op_def = Define `
driver_abs1_rx_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.ds_abs1_rx.temp_value];
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := abs1_rx_update |>`

val driver_abs1_rx_next_ready_op_def = Define `
driver_abs1_rx_next_ready_op (ds_abs1: ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with 
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.ds_abs1_rx.temp_value];
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := abs1_rx_ready |>`

val driver_abs1_rx_operations_def = Define `
driver_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_rx_ready) then
(driver_abs1_rx_ready_op ds_abs1)
else if (ds_abs1.state = abs1_rx_fetch_data) then
(driver_abs1_rx_fetch_data_op ds_abs1)
else if (ds_abs1.state = abs1_rx_next) then
(driver_abs1_rx_next_op ds_abs1)
else if (ds_abs1.state = abs1_rx_next_ready) then
(driver_abs1_rx_next_ready_op ds_abs1)
else ds_abs1 with err:= T`

(* other internal rx functions *)
val comb_abs1_rx_read_op_def = Define `
comb_abs1_rx_read_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_rx_fetch_data;
ds_abs1_rx := ds_abs1.ds_abs1_rx with temp_value := ds_abs1.spi_abs1.RX_SHIFT_REG |>`

val comb_abs1_rx_reset_op_def = Define `
comb_abs1_rx_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_ready`

val comb_abs1_rx_operations_def = Define `
comb_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.state = abs1_rx_read 
then (comb_abs1_rx_read_op ds_abs1)
else if ds_abs1.state = abs1_rx_reset
then (comb_abs1_rx_reset_op ds_abs1)
else ds_abs1 with err := T`

(* call_rx_ds_abs1: call ds_abs1 to apply rx mode. *)
val call_rx_ds_abs1_def = Define `
call_rx_ds_abs1 (ds_abs1:ds_abs1_state) (length: num) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_left_length := length; rx_data_buffer := [] |>;
state := abs1_rx_idle |>`

(* RX label related functions *)
val abs1_rx_receive_op_def = Define `
abs1_rx_receive_op (ds_abs1:ds_abs1_state) (data: word8 option) =
ds_abs1 with 
<| state := abs1_rx_update;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>`

val abs1_rx_fetch_data_op_def = Define `
abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) (data:word8 option) =
ds_abs1 with 
<| state := abs1_rx_next;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>`

val abs1_rx_receive_data_op_def = Define `
abs1_rx_receive_data_op (ds_abs1:ds_abs1_state) (data:word8 option) =
if (ds_abs1.state = abs1_rx_receive) then 
(abs1_rx_receive_op ds_abs1 data)
else if (ds_abs1.state = abs1_rx_fetch_data) then 
(abs1_rx_fetch_data_op ds_abs1 data)
else ds_abs1 with err := T`

val _ = export_theory();
