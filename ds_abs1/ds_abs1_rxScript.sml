open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs1_stateTheory;
open board_memTheory;

val _ = new_theory "ds_abs1_rx";

(* SPI_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_RX_ENABLE_def = Define `
SPI_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_rx.state = abs1_rx_idle) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_update) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_fetch_data) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_return) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_ready_for_reset))`

(* DRIVER_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_RX_ENABLE_def = Define `
DRIVER_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_rx.state = abs1_rx_idle) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_receive) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_update) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_ready) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_fetch_data) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_return) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_done))`

(* COMB_ABS1_RX_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_RX_ENABLE_def = Define `
COMB_ABS1_RX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_rx.state = abs1_rx_reset) \/
(ds_abs1.ds_abs1_rx.state = abs1_rx_ready_for_reset))`

(* tau_spi related functions *)
(* spi_abs1_rx_idle_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_idle_op_def = Define `
spi_abs1_rx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with
ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| state := abs1_rx_receive;
   rx_data_buffer := [] |>`

(* spi_abs1_rx_update_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_update_op_def = Define `
spi_abs1_rx_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
state := abs1_rx_ready`

(* spi_abs1_rx_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_fetch_data_op_def = Define `
spi_abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
state := abs1_rx_done`

(* spi_abs1_rx_return_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_return_op_def = Define `
spi_abs1_rx_return_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
state := abs1_rx_receive`

(* spi_abs1_rx_ready_for_reset_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_ready_for_reset_op_def = Define `
spi_abs1_rx_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
state := abs1_rx_reset`

(* spi_abs_rx_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_rx_operations_def = Define `
spi_abs1_rx_opearions (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_rx.state of
  | abs1_rx_pre => ds_abs1 with err := T
  | abs1_rx_idle => spi_abs1_rx_idle_op ds_abs1
  | abs1_rx_receive => ds_abs1 with err := T
  | abs1_rx_update => spi_abs1_rx_update_op ds_abs1
  | abs1_rx_ready => ds_abs1 with err := T
  | abs1_rx_fetch_data => spi_abs1_rx_fetch_data_op ds_abs1
  | abs1_rx_return => spi_abs1_rx_return_op ds_abs1
  | abs1_rx_done => ds_abs1 with err := T
  | abs1_rx_ready_for_reset => spi_abs1_rx_ready_for_reset_op ds_abs1
  | abs1_rx_reset => ds_abs1 with err := T`


(* tau_dr related functions *)
(* driver_abs1_rx_idle_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_idle_op_def = Define `
driver_abs1_rx_idle_op (ds_abs1:ds_abs1_state) = 
ds_abs1 with <| ds_abs1_rx := ds_abs1.ds_abs1_rx with
rx_data_buffer := [];
driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |> |>`

(* driver_abs1_rx_receive_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_receive_op_def = Define `
driver_abs1_rx_receive_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_rx_update_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_update_op_def = Define `
driver_abs1_rx_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_rx_ready_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_ready_op_def = Define `
driver_abs1_rx_ready_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_CH0STAT)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w))
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
     dr_abs1_last_read_v := (SOME 1w)
else ds_abs1 with 
<| ds_abs1_rx := ds_abs1.ds_abs1_rx with state := abs1_rx_fetch_data;
   driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT); dr_abs1_last_read_v := (SOME 1w) |> |>`

(* driver_abs1_rx_fetch_data_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_fetch_data_op_def = Define `
driver_abs1_rx_fetch_data_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| state := if ds_abs1.ds_abs1_rx.rx_left_length > 1 then abs1_rx_return
   else abs1_rx_ready_for_reset;
   rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG]; 
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>`

(* driver_abs1_return_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_return_op_def = Define `
driver_abs1_rx_return_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with
<| dr_abs1_last_read_ad := (SOME SPI0_CH0STAT);
   dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_rx_done_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_done_op_def = Define `
driver_abs1_rx_done_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| state := if ds_abs1.ds_abs1_rx.rx_left_length > 1 then abs1_rx_receive
   else abs1_rx_reset;
   rx_data_buffer := ds_abs1.ds_abs1_rx.rx_data_buffer ++ [ds_abs1.spi_abs1.RX_SHIFT_REG];
   rx_left_length := ds_abs1.ds_abs1_rx.rx_left_length - 1 |>`

(* driver_abs1_rx_operations: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_rx_operations_def = Define `
driver_abs1_rx_operations (ds_abs1:ds_abs1_state) =
case ds_abs1.ds_abs1_rx.state of
  | abs1_rx_pre => ds_abs1 with err := T
  | abs1_rx_idle => driver_abs1_rx_idle_op ds_abs1
  | abs1_rx_receive => driver_abs1_rx_receive_op ds_abs1
  | abs1_rx_update => driver_abs1_rx_update_op ds_abs1
  | abs1_rx_ready => driver_abs1_rx_ready_op ds_abs1
  | abs1_rx_fetch_data => driver_abs1_rx_fetch_data_op ds_abs1
  | abs1_rx_return => driver_abs1_rx_return_op ds_abs1
  | abs1_rx_done => driver_abs1_rx_done_op ds_abs1
  | abs1_rx_ready_for_reset => ds_abs1 with err := T
  | abs1_rx_reset => ds_abs1 with err := T`


(* tau_comb related functions *)
(* comb_abs1_rx_ready_for_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_rx_ready_for_reset_op_def = Define `
comb_abs1_rx_ready_for_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with state := abs1_rx_reset`

(* comb_abs1_rx_reset_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_rx_reset_op_def = Define `
comb_abs1_rx_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with state := abs1_rx_pre`

(* comb_abs1_rx_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_rx_operations_def = Define `
comb_abs1_rx_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.ds_abs1_rx.state = abs1_rx_ready_for_reset
then (comb_abs1_rx_ready_for_reset_op ds_abs1)
else if ds_abs1.ds_abs1_rx.state = abs1_rx_reset
then (comb_abs1_rx_reset_op ds_abs1)
else ds_abs1 with err := T`

(* call_rx_ds_abs1: ds_abs1_state -> num -> ds_abs1_state *)
val call_rx_ds_abs1_def = Define `
call_rx_ds_abs1 (ds_abs1:ds_abs1_state) (length: num) =
ds_abs1 with ds_abs1_rx := ds_abs1.ds_abs1_rx with
<| state := abs1_rx_idle;
rx_left_length := length |>`

(* RX label function *)
(* abs1_rx_receive_op: ds_abs1_state -> word8 option -> ds_abs1_state *)
val abs1_rx_receive_op_def = Define `
abs1_rx_receive_op (ds_abs1:ds_abs1_state) (data: word8 option) =
if (data <> NONE) then
ds_abs1 with 
<| ds_abs1_rx := ds_abs1.ds_abs1_rx with state := abs1_rx_update;
   spi_abs1 := ds_abs1.spi_abs1 with RX_SHIFT_REG := THE data |>
else ds_abs1`

val _ = export_theory();
