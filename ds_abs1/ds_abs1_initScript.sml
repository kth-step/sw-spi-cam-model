open HolKernel bossLib boolLib Parse;
open ds_abs1_stateTheory board_memTheory;

val _ = new_theory "ds_abs1_init";

(* SPI_ABS1_INIT_ENABLE: ds_abs1_state -> bool *)
val SPI_ABS1_INIT_ENABLE_def = Define `
SPI_ABS1_INIT_ENABLE (ds_abs1:ds_abs1_state) =
(ds_abs1.ds_abs1_init.state = abs1_init_start)`

(* DRIVER_ABS1_INIT_ENABLE: ds_abs1_state -> bool *)
val DRIVER_ABS1_INIT_ENABLE_def = Define `
DRIVER_ABS1_INIT_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.ds_abs1_init.state = abs1_init_start) \/
(ds_abs1.ds_abs1_init.state = abs1_init_check))`

(* COMB_ABS1_INIT_ENABLE: ds_abs1_state -> bool *)
val COMB_ABS1_INIT_ENABLE_def = Define `
COMB_ABS1_INIT_ENABLE (ds_abs1:ds_abs1_state) =
(ds_abs1.ds_abs1_init.state = abs1_init_done)`

(* spi_abs1_init_start_op: ds_abs1_state -> ds_abs1_state *)
val spi_abs1_init_start_op_def = Define `
spi_abs1_init_start_op (ds_abs1:ds_abs1_state) =
ds_abs1 with 
ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_check`
(*
<| ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_check;
spi_abs1 := ds_abs1.spi_abs1 with 
abs1_regs := ds_abs1.spi_abs1.abs1_regs with SYSSTATUS := 1w (* TO REMOVE *)|>`
*)

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

(* comb_abs1_init_done_op: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_init_done_op_def = Define `
comb_abs1_init_done_op (ds_abs1: ds_abs1_state) =
ds_abs1 with ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_start`
(*
<| ds_abs1_init := ds_abs1.ds_abs1_init with state := abs1_init_start;
spi_abs1 := ds_abs1.spi_abs1 with abs1_regs := ds_abs1.spi_abs1.abs1_regs
with SYSSTATUS := 0w |>`
*)

(* comb_abs1_init_operations: ds_abs1_state -> ds_abs1_state *)
val comb_abs1_init_operations_def = Define `
comb_abs1_init_operations (ds_abs1:ds_abs1_state) = 
if ds_abs1.ds_abs1_init.state = abs1_init_done 
then comb_abs1_init_done_op ds_abs1
else ds_abs1 with err := T`

(* call_init_ds_abs1:ds_abs1_state -> ds_abs1_state *)
val call_init_ds_abs1_def = Define `
call_init_ds_abs1 (ds_abs1:ds_abs1_state) =
ds_abs1 with ds_abs1_init := ds_abs1.ds_abs1_init with 
state := abs1_init_start`

val _ = export_theory();
