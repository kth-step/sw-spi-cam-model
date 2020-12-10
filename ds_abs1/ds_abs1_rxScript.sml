open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs1_stateTheory;

val _ = new_theory "ds_abs1_rx";

(* SPI_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_RX_ENABLE_def = Define `
SPI_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_idle) \/
(ds_abs1.state = abs1_rx_update) \/
(ds_abs1.state = abs1_rx_next) \/
(ds_abs1.state = abs1_rx_stop))`

(* DRIVER_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_RX_ENABLE_def = Define `
DRIVER_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_ready) \/
(ds_abs1.state = abs1_rx_fetch_data) \/
(ds_abs1.state = abs1_rx_next) \/
(ds_abs1.state = abs1_rx_next_ready))`

(* COMB_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_RX_ENABLE_def = Define `
COMB_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
(ds_abs1.state = abs1_rx_reset)`

(* ABS1_RX_LBL_ENABLE: ds_abs1_state -> bool *)
val ABS1_RX_LBL_ENABLE_def = Define `
ABS1_RX_LBL_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_rx_receive) \/
(ds_abs1.state = abs1_rx_fetch_data) \/
(ds_abs1.state = abs1_rx_done))`

(* tau_spi related functions *)
(* spi_abs1_rx_idle_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_idle_op_def = Define `
spi_abs1_rx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_receive`

(* spi_abs1_rx_update_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_update_op_def = Define `
spi_abs1_rx_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_ready`

(* spi_abs1_rx_next_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_next_op_def = Define `
spi_abs1_rx_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_next_ready`

(* spi_abs1_rx_stop_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_stop_op_def = Define `
spi_abs1_rx_stop_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_reset`

(* spi_abs_rx_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_operations_def = Define `
spi_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_rx_idle) then
(spi_abs1_rx_idle_op ds_abs1)
else if (ds_abs1.state = abs1_rx_update) then
(spi_abs1_rx_update_op ds_abs1)
else if (ds_abs1.state = abs1_rx_next) then
(spi_abs1_rx_next_op ds_abs1)
else if (ds_abs1.state = abs1_rx_stop) then
(spi_abs1_rx_stop_op ds_abs1)
else ds_abs1 with err := T`


(* tau_dr related functions *)
(* driver_abs1_rx_ready_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_ready_op_def = Define `
driver_abs1_rx_ready_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_rx_fetch_data`

(* driver_abs1_rx_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_fetch_data_op_def = Define `
driver_abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG]; 
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := if ds_abs1.ds_abs1_rx.rx_left_length > 1 then abs1_rx_done else abs1_rx_receive |>`

(* driver_abs1_rx_next_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_next_op_def = Define `
driver_abs1_rx_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.ds_abs1_rx.temp_value];
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := if ds_abs1.ds_abs1_rx.rx_left_length > 1 then abs1_rx_update else abs1_rx_stop |>`

(* driver_abs1_rx_next_ready_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_next_ready_op_def = Define `
driver_abs1_rx_next_ready_op (ds_abs1: ds_abs1_state) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with 
<| rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.ds_abs1_rx.temp_value];
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>;
state := if ds_abs1.ds_abs1_rx.rx_left_length > 1 then abs1_rx_ready else abs1_rx_reset |>`

(* driver_abs1_rx_operations: ds_abs1_state -> ds_abs1_state *)
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


(* tau_comb related functions *)
(* comb_abs1_rx_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_rx_reset_op_def = Define `
comb_abs1_rx_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_ready`

(* comb_abs1_rx_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_rx_operations_def = Define `
comb_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.state = abs1_rx_reset
then (comb_abs1_rx_reset_op ds_abs1)
else ds_abs1 with err := T`


(* call_rx_ds_abs1: ds_abs1_state -> num -> ds_abs1_state *)
val call_rx_ds_abs1_def = Define `
call_rx_ds_abs1 (ds_abs1:ds_abs1_state) (length: num) =
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| rx_left_length := length; rx_data_buffer := [] |>;
state := abs1_rx_idle |>`


(* RX label function *)
(* abs1_rx_receive_op: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_rx_receive_op_def = Define `
abs1_rx_receive_op (ds_abs1:ds_abs1_state) (data: word8 option) =
ds_abs1 with 
<| state := abs1_rx_update;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>`

(* abs1_rx_fetch_data_op: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_rx_fetch_data_op_def = Define `
abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) (data:word8 option) =
ds_abs1 with 
<| state := abs1_rx_next;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data;
   ds_abs1_rx := ds_abs1.ds_abs1_rx with temp_value := ds_abs1.spi_abs1.RX_SHIFT_REG |>`

(* abs1_rx_done_op: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_rx_done_op_def = Define `
abs1_rx_done_op (ds_abs1:ds_abs1_state) (data:word8 option) =
ds_abs1 with 
<| state := abs1_rx_stop;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>`


(* abs1_rx_receive_data_op: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_rx_receive_data_op_def = Define `
abs1_rx_receive_data_op (ds_abs1:ds_abs1_state) (data:word8 option) =
if (ds_abs1.state = abs1_rx_receive) then 
(abs1_rx_receive_op ds_abs1 data)
else if (ds_abs1.state = abs1_rx_fetch_data) then 
(abs1_rx_fetch_data_op ds_abs1 data)
else if (ds_abs1.state = abs1_rx_done) then 
(abs1_rx_done_op ds_abs1 data)
else ds_abs1 with err := T`

val _ = export_theory();
