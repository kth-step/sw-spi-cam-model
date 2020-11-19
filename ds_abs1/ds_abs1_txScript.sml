open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs1_stateTheory;
open board_memTheory;

val _ = new_theory "ds_abs1_tx";

(* SPI_ABS1_TX_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_TX_ENABLE_def = Define `
SPI_ABS1_TX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_tx.state = abs1_tx_idle) \/ 
(ds_abs1.ds_abs1_tx.state = abs1_tx_trans) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_check_1) \/ 
(ds_abs1.ds_abs1_tx.state = abs1_tx_check_3) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_next) \/ 
(ds_abs1.ds_abs1_tx.state = abs1_tx_ready_for_reset))`

(* DRIVER_ABS1_TX_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_TX_ENABLE_def = Define `
DRIVER_ABS1_TX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_tx.state = abs1_tx_idle) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_prepare) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_trans) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_done_1) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_done_2) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_check_1) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_check_2) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_check_3))`

(* COMB_ABS1_TX_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_TX_ENABLE_def = Define `
COMB_ABS1_TX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_tx.state = abs1_tx_reset) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_ready_for_reset))`

(* tau_spi related functions *)
(* spi_abs1_tx_idle_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_idle_op_def = Define `
spi_abs1_tx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with
ds_abs1_tx := ds_abs1.ds_abs1_tx with 
state := abs1_tx_prepare`

(* spi_abs1_tx_trans_op: ds_abs1_state -> ds_abs1_state *)
(* false for bi-simulation, to change *)
val spi_abs1_tx_trans_op_def = Define `
spi_abs1_tx_trans_op (ds_abs1:ds_abs1_state) =
ds_abs1 with
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with
<| state := if ds_abs1.ds_abs1_tx.tx_left_length > 1 then abs1_tx_done_2 
   else abs1_tx_done_1;
   tx_data_buffer := TL ds_abs1.ds_abs1_tx.tx_data_buffer;
   tx_left_length := ds_abs1.ds_abs1_tx.tx_left_length - 1 |>;
   spi_abs1 := ds_abs1.spi_abs1 with 
   TX_SHIFT_REG := HD ds_abs1.ds_abs1_tx.tx_data_buffer |>`

(* spi_abs1_check_1_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_check_1_op_def = Define `
spi_abs1_tx_check_1_op (ds_abs1:ds_abs1_state) = 
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with
state := abs1_tx_check_2`

(* spi_abs1_check_3_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_check_3_op_def = Define `
spi_abs1_tx_check_3_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with
state := abs1_tx_prepare`

(* spi_abs1_tx_next_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_next_op_def = Define `
spi_abs1_tx_next_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with
state := abs1_tx_trans`

(* spi_abs1_tx_reset_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_ready_for_reset_op_def = Define `
spi_abs1_tx_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with
state := abs1_tx_reset`

(* spi_abs1_tx_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_tx_operations_def = Define `
spi_abs1_tx_operations (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_tx.state of
  | abs1_tx_pre => ds_abs1 with err := T
  | abs1_tx_idle => spi_abs1_tx_idle_op ds_abs1
  | abs1_tx_prepare => ds_abs1 with err := T
  | abs1_tx_trans => spi_abs1_tx_trans_op ds_abs1
  | abs1_tx_done_1 => ds_abs1 with err := T
  | abs1_tx_done_2 => ds_abs1 with err := T
  | abs1_tx_done_3 => ds_abs1 with err := T
  | abs1_tx_check_1 => spi_abs1_tx_check_1_op ds_abs1
  | abs1_tx_check_2 => ds_abs1 with err := T
  | abs1_tx_check_3 => spi_abs1_tx_check_3_op ds_abs1
  | abs1_tx_next => spi_abs1_tx_next_op ds_abs1
  | abs1_tx_ready_for_reset => spi_abs1_tx_ready_for_reset_op ds_abs1 
  | abs1_tx_reset => ds_abs1 with err := T`


(* tau_dr related functions *)
(* driver_abs1_tx_idle_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_idle_op_def = Define `
driver_abs1_tx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| ds_abs1_tx := ds_abs1.ds_abs1_tx with 
tx_left_length := LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer;
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 0w) |> |>`

(* driver_abs1_tx_prepare_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_prepare_op_def = Define `
driver_abs1_tx_prepare_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_CH0STAT)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w))
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
     dr_abs1_last_read_v := (SOME 2w)
else ds_abs1 with
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_trans;
   driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 2w)|> |>`

(* driver_abs1_tx_trans_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_trans_op_def = Define `
driver_abs1_tx_trans_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_tx_done_1_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_done_1_op_def = Define `
driver_abs1_tx_done_1_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_tx_done_2_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_done_2_op_def = Define `
driver_abs1_tx_done_2_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_CH0STAT)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w))
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
     dr_abs1_last_read_v := (SOME 2w)
else ds_abs1 with
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_done_3;
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 2w)|> |>`

(* driver_abs1_tx_check_1_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_check_1_op_def = Define `
driver_abs1_tx_check_1_op (ds_abs1:ds_abs1_state) =
ds_abs1 with
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_ready_for_reset;
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 6w) |> |>`

(* driver_abs1_tx_check_2_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_check_2_op_def = Define `
driver_abs1_tx_check_2_op (ds_abs1:ds_abs1_state) =
ds_abs1 with 
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_reset;
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 6w) |> |>`

(* driver_abs1_tx_check_3_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_check_3_op_def = Define `
driver_abs1_tx_check_3_op (ds_abs1:ds_abs1_state) =
ds_abs1 with 
<| ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_next;
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 2w) |> |>`

(* driver_abs1_tx_operations: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_tx_operations_def = Define `
driver_abs1_tx_operations (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_tx.state of
  | abs1_tx_pre => ds_abs1 with err := T
  | abs1_tx_idle =>  driver_abs1_tx_idle_op ds_abs1
  | abs1_tx_prepare => driver_abs1_tx_prepare_op ds_abs1
  | abs1_tx_trans => driver_abs1_tx_trans_op ds_abs1
  | abs1_tx_done_1 => driver_abs1_tx_done_1_op ds_abs1
  | abs1_tx_done_2 => driver_abs1_tx_done_2_op ds_abs1
  | abs1_tx_done_3 => ds_abs1 with err := T
  | abs1_tx_check_1 => driver_abs1_tx_check_1_op ds_abs1
  | abs1_tx_check_2 => driver_abs1_tx_check_2_op ds_abs1
  | abs1_tx_check_3 => driver_abs1_tx_check_3_op ds_abs1 
  | abs1_tx_next => ds_abs1 with err := T
  | abs1_tx_ready_for_reset => ds_abs1 with err := T
  | abs1_tx_reset => ds_abs1 with err := T`


(* tau_comb related functions *)
(* comb_abs1_tx_ready_for_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_tx_ready_for_reset_op_def = Define `
comb_abs1_tx_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_reset`

(* comb_abs1_tx_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_tx_reset_op_def = Define `
comb_abs1_tx_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_pre`

(* comb_abs1_tx_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_tx_operations_def = Define `
comb_abs1_tx_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.ds_abs1_tx.state = abs1_tx_ready_for_reset
then (comb_abs1_tx_ready_for_reset_op ds_abs1)
else if ds_abs1.ds_abs1_tx.state = abs1_tx_reset 
then (comb_abs1_tx_reset_op ds_abs1)
else ds_abs1 with err := T`

(* ds_abs1 is in a good state to transmit a byte
 * ABS1_TX_LBL_ENABLE: ds_abs1_state -> bool
 *)
val ABS1_TX_LBL_ENABLE_def = Define `
ABS1_TX_LBL_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_tx.state = abs1_tx_done_1) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_done_2) \/
(ds_abs1.ds_abs1_tx.state = abs1_tx_done_3))`

(* abs1_tx_trans_done_op: ds_abs1_state -> ds_abs1_state * word8 option *)
val abs1_tx_trans_done_op_def = Define `
abs1_tx_trans_done_op (ds_abs1:ds_abs1_state) =
if ds_abs1.ds_abs1_tx.state = abs1_tx_done_1 then
(ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_check_1,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else if ds_abs1.ds_abs1_tx.state = abs1_tx_done_2 then
(ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_check_3,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else if ds_abs1.ds_abs1_tx.state = abs1_tx_done_3 then
(ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_next,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else (ds_abs1, NONE)`

(* abs1_tx_trans_done_op_value: ds_abs1_state -> word8 option *)
val abs1_tx_trans_done_op_value_def = Define `
abs1_tx_trans_done_op_value (ds_abs1:ds_abs1_state) =
let (ds_abs1', v) = (abs1_tx_trans_done_op ds_abs1)
in v`

(* abs1_tx_trans_done_op_state: ds_abs1_state -> ds_abs1_state *)
val abs1_tx_trans_done_op_state_def = Define `
abs1_tx_trans_done_op_state (ds_abs1:ds_abs1_state) =
let (ds_abs1', v) = (abs1_tx_trans_done_op ds_abs1)
in ds_abs1'`

(* call_tx_ds_abs1: ds_abs1_state -> word8 list -> ds_abs1_state *)
val call_tx_ds_abs1_def = Define `
call_tx_ds_abs1 (ds_abs1:ds_abs1_state) (buffer:word8 list) =
ds_abs1 with ds_abs1_tx := ds_abs1.ds_abs1_tx with
<| state := abs1_tx_idle;
   tx_data_buffer := buffer |>`

val _ = export_theory();
