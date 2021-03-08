open HolKernel bossLib boolLib Parse;
open ds_abs1_stateTheory;

val _ = new_theory "ds_abs1_init";

(* call_init_ds_abs1: call ds_abs1 to initialize *)
val call_init_ds_abs1_def = Define `
call_init_ds_abs1 (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_init_start`

(* COMB_ABS1_INIT_ENABLE: ds_abs1's state is permitted to call init *)
val COMB_ABS1_INIT_ENABLE_def = Define `
COMB_ABS1_INIT_ENABLE (ds_abs1:ds_abs1_state) =
(ds_abs1.state = abs1_init_start)`

(* comb_abs1_init_start_op: internal operation *)
val comb_abs1_init_start_op_def = Define `
comb_abs1_init_start_op (ds_abs1: ds_abs1_state) =
ds_abs1 with state := abs1_ready`

(* comb_abs1_init_operations: perform the internal operations for init *)
val comb_abs1_init_operations_def = Define `
comb_abs1_init_operations (ds_abs1:ds_abs1_state) = 
if (ds_abs1.state = abs1_init_start) then
(comb_abs1_init_start_op ds_abs1)
else ds_abs1 with err := T`

val _ = export_theory();
