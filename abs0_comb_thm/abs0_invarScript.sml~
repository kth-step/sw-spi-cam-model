open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory ds_abs0_initTheory ds_abs0_relTheory;

val _ = new_theory "init_correct";

(* abs0 init correctness: from the start or ready state, abs0 can be initialized with a call, and then it's ready to work *)
val abs0_init_correct = store_thm("abs0_init_correct",
``!ds_abs0.
ds_abs0.state = abs0_init \/ ds_abs0.state = abs0_ready ==> 
?ds_abs0'. ds_abs0_tr ds_abs0 call_init ds_abs0' /\ ds_abs0'.state = abs0_ready``,
rw [ds_abs0_tr_cases, ABS0_CALL_INIT_ENABLE_def, call_init_ds_abs0_def]);

val _ = export_theory();
