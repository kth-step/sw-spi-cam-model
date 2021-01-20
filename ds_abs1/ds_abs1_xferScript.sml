open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs1_stateTheory;

val _ = new_theory "ds_abs1_xfer";

(* SPI_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_XFER_ENABLE_def = Define `
SPI_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_xfer_idle) \/
(ds_abs1.state = abs1_xfer_data) \/
(ds_abs1.state = abs1_xfer_update))`

(* DRIVER_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_XFER_ENABLE_def = Define `
DRIVER_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
(ds_abs1.state = abs1_xfer_fetch_data)`

(* COMB_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_XFER_ENABLE_def = Define `
COMB_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_xfer_prepare) \/
(ds_abs1.state = abs1_xfer_ready) \/
(ds_abs1.state = abs1_xfer_reset))`


(* tau_spi related functions *)
(* spi_abs1_xfer_idle_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_idle_op_def = Define `
spi_abs1_xfer_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_xfer_prepare`

(* spi_abs1_xfer_data_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_data_op_def = Define `
spi_abs1_xfer_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_xfer_exchange; 
spi_abs1 := ds_abs1.spi_abs1 with
TX_SHIFT_REG := (EL (ds_abs1.ds_abs1_xfer.xfer_cur_length - 1) 
(ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer))|>`

(* spi_abs1_xfer_update_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_update_op_def = Define `
spi_abs1_xfer_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_xfer_ready`

(* spi_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_operations_def = Define `
spi_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_xfer_idle) then
(spi_abs1_xfer_idle_op ds_abs1)
else if (ds_abs1.state = abs1_xfer_data) then
(spi_abs1_xfer_data_op ds_abs1)
else if (ds_abs1.state = abs1_xfer_update) then
(spi_abs1_xfer_update_op ds_abs1)
else ds_abs1 with err := T`


(* tau_driver related functions *)
(* driver_abs1_xfer_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_fetch_data_op_def = Define `
driver_abs1_xfer_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with 
xfer_dataIN_buffer := ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG];
state := if ds_abs1.ds_abs1_xfer.xfer_cur_length < (LENGTH (ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer)) 
then abs1_xfer_prepare else abs1_xfer_reset |>`

(* driver_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_operations_def = Define `
driver_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_xfer_fetch_data) then
(driver_abs1_xfer_fetch_data_op ds_abs1)
else ds_abs1 with err := T`


(* tau_comb related functions *)
(* comb_abs1_xfer_prepare_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_prepare_op_def = Define `
comb_abs1_xfer_prepare_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with 
xfer_cur_length := ds_abs1.ds_abs1_xfer.xfer_cur_length + 1;
state := abs1_xfer_data |>`

(* comb_abs1_xfer_ready_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_ready_op_def = Define `
comb_abs1_xfer_ready_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_xfer_fetch_data`

(* comb_abs1_xfer_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_reset_op_def = Define `
comb_abs1_xfer_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_ready`

(* comb_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_operations_def = Define `
comb_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.state = abs1_xfer_prepare 
then (comb_abs1_xfer_prepare_op ds_abs1)
else if (ds_abs1.state = abs1_xfer_ready)
then (comb_abs1_xfer_ready_op ds_abs1)
else if (ds_abs1.state = abs1_xfer_reset)
then (comb_abs1_xfer_reset_op ds_abs1)
else ds_abs1 with err := T`

(* XFER label functions *)
(* abs1_xfer_exchange_op: ds_abs1_state -> word8 option -> ds_abs1_state * word8 option *)
val abs1_xfer_exchange_op_def = Define `
abs1_xfer_exchange_op (ds_abs1:ds_abs1_state) (data: word8 option) =
if (data <> NONE) then
(ds_abs1 with
<| state := abs1_xfer_update;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else (ds_abs1 with err := T, NONE)`

(* abs1_xfer_exchange_op_value: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_xfer_exchange_op_value_def = Define `
abs1_xfer_exchange_op_value (ds_abs1:ds_abs1_state) (data:word8 option) =
let (ds_abs1', v) = (abs1_xfer_exchange_op ds_abs1 data) in
v`

(* abs1_xfer_exchange_op_state: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_xfer_exchange_op_state_def = Define `
abs1_xfer_exchange_op_state (ds_abs1:ds_abs1_state) (data:word8 option) =
let (ds_abs1', v) = (abs1_xfer_exchange_op ds_abs1 data) in
ds_abs1'`

(* call_xfer_ds_abs1: ds_abs1_state -> word8 list -> ds_abs1_state *)
val call_xfer_ds_abs1_def = Define `
call_xfer_ds_abs1 (ds_abs1:ds_abs1_state) (buffer:word8 list) =
ds_abs1 with <| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
<| xfer_dataOUT_buffer := buffer;
   xfer_dataIN_buffer := [];
   xfer_cur_length := 0 |>;
state := abs1_xfer_idle |>`

val _ = export_theory();
