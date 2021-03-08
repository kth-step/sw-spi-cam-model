open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory;

val _ = new_theory "ds_abs0_init";

(* ABS0_CALL_INIT_ENABLE: ds_abs0 is permitted to initialize. *)
val ABS0_CALL_INIT_ENBLE_def = Define `
ABS0_CALL_INIT_ENABLE (ds_abs0:ds_abs0_state) =
((ds_abs0.state = abs0_init) \/
(ds_abs0.state = abs0_ready))`

(* call_init_ds_abs0: call ds_abs0 to apply initialization. *)
val call_init_ds_abs0_def = Define `
call_init_ds_abs0 (ds_abs0:ds_abs0_state) =
ds_abs0 with state := abs0_ready`

val _ = export_theory();
