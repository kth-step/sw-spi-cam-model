open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory ds_abs0_initTheory ds_abs0_relTheory;

val _ = new_theory "init_correct";

val abs0_init_correct = store_thm("abs0_init_correct",
``!ds_abs0.
ds_abs0.state = abs0_init \/ ds_abs0.state = abs0_ready ==> 
?ds_abs0'. ds_abs0_tr ds_abs0 call_init ds_abs0' /\ ds_abs0'.state = abs0_ready``,
rw [ds_abs0_tr_cases, ABS0_CALL_INIT_ENABLE_def, call_init_ds_abs0_def]);

DR_INIT spi_init --> dr_ready and spi_ready
weak_bisim r1 concrete_spi_dr abs1_spi_dr ==>
weak_bisim r2 double_concrete (concrete_spi_dr) double_abs1 (abs1_spi_dr) 

spi_dr

r2 tr3 tr4
weak_bisim r3 tr1 tr3

val _ = export_theory();
