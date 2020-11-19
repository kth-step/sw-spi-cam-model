open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs1_stateTheory;
open board_memTheory;

val _ = new_theory "ds_abs1_xfer";

(* SPI_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_XFER_ENABLE_def = Define `
SPI_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_idle) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_trans) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_update) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_fetch_data) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_next) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_next_write) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready_for_reset))`

(* DRIVER_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_XFER_ENABLE_def = Define `
DRIVER_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_idle) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_prepare) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_trans) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_exchange) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_update) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_fetch_data) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_next) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_done))`

(* COMB_ABS1_XFER_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_XFER_ENABLE_def = Define `
COMB_ABS1_XFER_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready_for_reset) \/
(ds_abs1.ds_abs1_xfer.state = abs1_xfer_reset))`

(* tau_spi related functions *)
(* spi_abs1_xfer_idle_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_idle_op_def = Define `
spi_abs1_xfer_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_prepare`

(* spi_abs1_xfer_trans_op: ds_abs1_state -> ds_abs1_state *)
(* TO-FIX false for bi-simulation *)
val spi_abs1_xfer_trans_op_def = Define `
spi_abs1_xfer_trans_op (ds_abs1:ds_abs1_state) =
ds_abs1 with
<| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
<| state := abs1_xfer_exchange;
   xfer_dataOUT_buffer := TL ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer;
   xfer_left_length := ds_abs1.ds_abs1_xfer.xfer_left_length - 1 |>;
   spi_abs1 := ds_abs1.spi_abs1 with
   TX_SHIFT_REG := HD ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer |>`

(* spi_abs1_xfer_update_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_update_op_def = Define `
spi_abs1_xfer_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_ready`

(* spi_abs1_xfer_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_fetch_data_op_def = Define `
spi_abs1_xfer_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_done`

(* spi_abs1_xfer_next_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_next_op_def = Define `
spi_abs1_xfer_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_prepare`

(* spi_abs1_xfer_next_write_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_next_write_op_def = Define `
spi_abs1_xfer_next_write_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_trans`

(* spi_abs1_xfer_ready_for_reset_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_ready_for_reset_op_def = Define `
spi_abs1_xfer_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_reset`

(* spi_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_xfer_operations_def = Define `
spi_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_xfer.state of 
  | abs1_xfer_pre => ds_abs1 with err := T
  | abs1_xfer_idle => spi_abs1_xfer_idle_op ds_abs1
  | abs1_xfer_prepare => ds_abs1 with err := T
  | abs1_xfer_trans => spi_abs1_xfer_trans_op ds_abs1
  | abs1_xfer_exchange => ds_abs1 with err := T
  | abs1_xfer_update => spi_abs1_xfer_update_op ds_abs1
  | abs1_xfer_ready => ds_abs1 with err := T
  | abs1_xfer_fetch_data => spi_abs1_xfer_fetch_data_op ds_abs1
  | abs1_xfer_next => spi_abs1_xfer_next_op ds_abs1
  | abs1_xfer_next_write => spi_abs1_xfer_next_write_op ds_abs1
  | abs1_xfer_done => ds_abs1 with err := T
  | abs1_xfer_ready_fot_reset => spi_abs1_xfer_ready_for_reset_op ds_abs1
  | abs1_xfer_reset => ds_abs1 with err := T`


(* tau_driver related functions *)
(* driver_abs1_xfer_idle_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_idle_op_def = Define `
driver_abs1_xfer_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
<| xfer_dataIN_buffer := [];
   xfer_left_length := LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer |>;
   driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |> |>`

(* driver_abs1_xfer_prepare_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_prepare_op_def = Define `
driver_abs1_xfer_prepare_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_CH0STAT)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w))
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
     dr_abs1_last_read_v := (SOME 2w)
else ds_abs1 with 
<| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with state := abs1_xfer_trans;
   driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 2w) |> |>`

(* driver_abs1_xfer_trans_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_trans_op_def = Define `
driver_abs1_xfer_trans_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_xfer_exchange_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_exchange_op_def = Define `
driver_abs1_xfer_exchange_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_xfer_update_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_update_op_def = Define `
driver_abs1_xfer_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_xfer_ready_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_ready_op_def = Define `
driver_abs1_xfer_ready_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_CH0STAT)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w))
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
     dr_abs1_last_read_v := (SOME 1w)
else ds_abs1 with
<| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with state := abs1_xfer_fetch_data;
   driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 1w) |> |> `

(* driver_abs1_xfer_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_fetch_data_op_def = Define `
driver_abs1_xfer_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with 
<| state := if ds_abs1.ds_abs1_xfer.xfer_left_length > 0 then abs1_xfer_next
   else abs1_xfer_ready_for_reset;
   xfer_dataIN_buffer := ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG] |>`

(* driver_abs1_xfer_next_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_next_op_def = Define `
driver_abs1_xfer_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_next_write`

(* driver_abs1_xfer_done_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_done_op_def = Define `
driver_abs1_xfer_done_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
<| state := if ds_abs1.ds_abs1_xfer.xfer_left_length > 0 then abs1_xfer_prepare
   else abs1_xfer_reset;
   xfer_dataIN_buffer := ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG] |>`

(* driver_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_xfer_operations_def = Define `
driver_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_xfer.state of
  | abs1_xfer_pre => ds_abs1 with err := T
  | abs1_xfer_idle => driver_abs1_xfer_idle_op ds_abs1
  | abs1_xfer_prepare => driver_abs1_xfer_prepare_op ds_abs1
  | abs1_xfer_trans => driver_abs1_xfer_trans_op ds_abs1
  | abs1_xfer_exchange => driver_abs1_xfer_exchange_op ds_abs1
  | abs1_xfer_update => driver_abs1_xfer_update_op ds_abs1
  | abs1_xfer_ready => driver_abs1_xfer_ready_op ds_abs1
  | abs1_xfer_fetch_data => driver_abs1_xfer_fetch_data_op ds_abs1
  | abs1_xfer_next => driver_abs1_xfer_next_op ds_abs1
  | abs1_xfer_next_write => ds_abs1 with err := T
  | abs1_xfer_done => driver_abs1_xfer_done_op ds_abs1
  | abs1_xfer_ready_for_reset => ds_abs1 with err := T
  | abs1_xfer_reset => ds_abs1 with err := T`


(* tau_comb related functions *)
(* comb_abs1_xfer_ready_for_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_ready_for_reset_op_def = Define `
comb_abs1_xfer_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with 
state := abs1_xfer_reset`

(* comb_abs1_xfer_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_reset_op_def = Define `
comb_abs1_xfer_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
state := abs1_xfer_pre`

(* comb_abs1_xfer_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_xfer_operations_def = Define `
comb_abs1_xfer_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready_for_reset
then (comb_abs1_xfer_ready_for_reset_op ds_abs1)
else if ds_abs1.ds_abs1_xfer.state = abs1_xfer_reset
then (comb_abs1_xfer_reset_op ds_abs1)
else ds_abs1 with err := T`

(* XFER label functions *)
(* abs1_xfer_exchange_op: ds_abs1_state -> word8 option *)
val abs1_xfer_exchange_op_def = Define `
abs1_xfer_exchange_op (ds_abs1:ds_abs1_state) (data: word8 option) =
if (data <> NONE) then
(ds_abs1 with
<| ds_abs1_xfer := ds_abs1.ds_abs1_xfer with state := abs1_xfer_update;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else (ds_abs1, NONE)`

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
ds_abs1 with ds_abs1_xfer := ds_abs1.ds_abs1_xfer with
<| state := abs1_xfer_idle;
   xfer_dataOUT_buffer := buffer;
   xfer_dataIN_buffer := [];
   xfer_left_length := LENGTH buffer |>`

val _ = export_theory();
