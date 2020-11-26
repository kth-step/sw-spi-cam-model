open HolKernel bossLib boolLib Parse;
open ds_abs1_stateTheory board_memTheory;

val _ = new_theory "ds_abs1_init";

(* COMB_ABS1_INIT_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_INIT_ENABLE_def = Define `
COMB_ABS1_INIT_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_init.state = abs1_init_start) \/
(ds_abs1.ds_abs1_init.state = abs1_init_done))`


(* spi_abs1_init_start_op: ds_abs1_state -> ds_abs1_state 
val spi_abs1_init_start_op_def = Define `
spi_abs1_init_start_op (ds_abs1:ds_abs1_state) =
ds_abs1 with 
ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_check`


(* spi_abs1_init_operations: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_init_operations_def = Define `
spi_abs1_init_operations (ds_abs1:ds_abs1_state) = 
if ds_abs1.ds_abs1_init.state = abs1_init_start then spi_abs1_init_start_op ds_abs1
else ds_abs1 with err := T`

(* driver_abs1_init_start_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_init_start_op_def = Define `
driver_abs1_init_start_op (ds_abs1:ds_abs1_state) =
ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with 
<| dr_abs1_last_read_ad := (SOME SPI0_SYSSTATUS); dr_abs1_last_read_v := (SOME 0w) |>`

(* driver_abs1_init_check_op: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_init_check_op_def = Define `
driver_abs1_init_check_op (ds_abs1:ds_abs1_state) =
if (ds_abs1.driver_abs1.dr_abs1_last_read_ad = (SOME SPI0_SYSSTATUS)) /\
   (ds_abs1.driver_abs1.dr_abs1_last_read_v = (SOME 0w)) 
then ds_abs1 with driver_abs1 := ds_abs1.driver_abs1 with 
     dr_abs1_last_read_v := (SOME 1w)
else ds_abs1 with 
<| ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_done;
driver_abs1 := ds_abs1.driver_abs1 with 
<| dr_abs1_last_read_ad := (SOME SPI0_SYSSTATUS); dr_abs1_last_read_v := (SOME 1w) |> |>`

(* driver_abs1_init_operations: ds_abs1_state -> ds_abs1_state *)
val driver_abs1_init_operations_def = Define `
driver_abs1_init_operations (ds_abs1:ds_abs1_state) = 
case ds_abs1.ds_abs1_init.state of
  | abs1_init_start => driver_abs1_init_start_op ds_abs1
  | abs1_init_check => driver_abs1_init_check_op ds_abs1
  | abs1_init_done => ds_abs1 with err := T`
*)

(* comb_abs1_init_start_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_init_start_op_def = Define `
comb_abs1_init_start_op (ds_abs1: ds_abs1_state) =
ds_abs1 with <|
ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_done;
ds_abs1_tx := ds_abs1.ds_abs1_tx with state := abs1_tx_pre;
ds_abs1_rx := ds_abs1.ds_abs1_rx with state := abs1_rx_pre;
ds_abs1_xfer := ds_abs1.ds_abs1_xfer with state := abs1_xfer_pre |>`


(* comb_abs1_init_done_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_init_done_op_def = Define `
comb_abs1_init_done_op (ds_abs1: ds_abs1_state) =
ds_abs1 with ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_start`


(* comb_abs1_init_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_init_operations_def = Define `
comb_abs1_init_operations (ds_abs1:ds_abs1_state) = 
case ds_abs1.ds_abs1_init.state of
  | abs1_init_pre => ds_abs1 with err := T
  | abs1_init_start => comb_abs1_init_start_op ds_abs1
  | abs1_init_done => comb_abs1_init_done_op ds_abs1`

(* call_init_ds_abs1:ds_abs1_state -> ds_abs1_state *)
val call_init_ds_abs1_def = Define `
call_init_ds_abs1 (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_init := ds_abs1.ds_abs1_init with 
state := abs1_init_start`

val _ = export_theory();
