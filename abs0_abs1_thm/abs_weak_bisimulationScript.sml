open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open ds_abs0_relTheory abs_relTheory;
open ds_abs1_relTheory;
open abs_rel_holds_call_lblTheory;

val _ = new_theory "abs_weak_bisimulation";

(* weak bisimulation between ds_abs0 and ds_abs1 *)
(* have to rewrite *)
val abs0_weak_bisimulation = store_thm("abs0_weak_bisimulation",
``!ds_abs0 ds_abs1 lbl ds_abs0'.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0_tr ds_abs0 lbl ds_abs0') ==>
?ds_abs1'. (ds_abs1_abs_tr ds_abs1 lbl ds_abs1') /\ (abs_rel ds_abs0' ds_abs1')``,
rw [ds_abs0_tr_cases] >>
rw [abs0_abs_rel_call_init, abs0_abs_rel_call_tx, abs0_abs_rel_call_rx,
abs0_abs_rel_call_xfer] >>
cheat);


val abs1_weak_bisimulation = store_thm("abs1_weak_bisimulation",
``!ds_abs0 ds_abs1 lbl ds_abs1'.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1_tr ds_abs1 lbl ds_abs1') ==>
(abs_rel ds_abs0 ds_abs1') \/
(?ds_abs0'. (ds_abs0_tr ds_abs0 lbl ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'))``,
rw [ds_abs1_tr_cases] >>
rw [abs1_init_pre_abs_rel_call_init, abs1_ready_abs_rel_call_init, 
abs1_abs_rel_call_tx, abs1_abs_rel_call_rx, abs1_abs_rel_call_xfer] >>
cheat);

val _ = export_theory();
