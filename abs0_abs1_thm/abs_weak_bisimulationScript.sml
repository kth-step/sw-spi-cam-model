open HolKernel bossLib boolLib Parse;
open SPI_stateTheory weak_bisimulationTheory;
open ds_abs0_relTheory abs_relTheory;
open ds_abs1_relTheory;
open abs_rel_holds_abs1_tau_spiTheory abs_rel_holds_abs1_tau_drTheory abs_rel_holds_abs1_tau_combTheory abs_rel_holds_call_lblTheory abs_rel_holds_TX_lblTheory abs_rel_holds_RX_lblTheory abs_rel_holds_XFER_lblTheory abs_rel_holds_abs0_tauTheory;

val _ = new_theory "abs_weak_bisimulation";

(*
val f_def = Define `
f a = (T \/ (f a))`
*)

(* a state can be reached after n tau steps 
val n_tau_tr_def = Define `
(n_tau_tr (0:num) (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = (tr s lbl s')) /\
(n_tau_tr (n:num) (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = ?(s'':'a). (tr s tau s'') /\ (n_tau_tr (n-1) tr s'' lbl s'))`

(* define the weak transition relation *)
val weak_tr_def = Define `
weak_tr (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = 
((tr s lbl s') \/
(s = s' /\ lbl = tau) \/
(?n. n_tau_tr n tr s lbl s'))`

(* define the weak bisimulation realtion *)
val weak_bisim_def = Define `
weak_bisim (r:'a -> 'b -> bool) (tr1:'a -> global_lbl_type -> 'a -> bool) (tr2:'b -> global_lbl_type -> 'b -> bool) =
(!s1 s2. r s1 s2 ==>
(!lbl s1'. tr1 s1 lbl s1' ==> ?s2'. weak_tr tr2 s2 lbl s2' /\ r s1' s2') /\
(!lbl s2'. tr2 s2 lbl s2' ==> ?s1'. weak_tr tr1 s1 lbl s1' /\ r s1' s2'))`
*)

val abs0_weak_simulation = store_thm("abs0_weak_simulation",
``!ds_abs0 ds_abs1 lbl ds_abs0'.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0_tr ds_abs0 lbl ds_abs0') ==>
(?ds_abs1'.(ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (abs_rel ds_abs0' ds_abs1')) \/
(?n ds_abs1'. (n_tau_tr n ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (abs_rel ds_abs0' ds_abs1'))``,
rw [ds_abs0_tr_cases] >> 
rw [abs0_abs_rel_call_init, abs0_abs_rel_call_tx, abs0_abs_rel_call_rx,
abs0_abs_rel_call_xfer, abs_rel_holds_abs_tau, abs_rel_holds_abs0_TX_lbl, 
abs_rel_holds_abs0_RX_lbl, abs_rel_holds_abs0_XFER_lbl]
(* TO PROVE: TX labels *));

val abs1_weak_simulation = store_thm("abs1_weak_simulation",
``!ds_abs0 ds_abs1 lbl ds_abs1'.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1_tr ds_abs1 lbl ds_abs1') ==>
(lbl = tau ==> 
(abs_rel ds_abs0 ds_abs1') \/
(?ds_abs0'. (ds_abs0_tr ds_abs0 lbl ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'))) /\
(lbl <> tau ==> 
?ds_abs0'. (ds_abs0_tr ds_abs0 lbl ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'))``,
rw [ds_abs1_tr_cases] >> 
rw [abs1_init_pre_abs_rel_call_init, abs1_ready_abs_rel_call_init, 
abs1_abs_rel_call_tx, abs1_abs_rel_call_rx, abs1_abs_rel_call_xfer,
abs_rel_holds_abs1_TX_lbl, abs_rel_holds_abs1_RX_lbl, abs_rel_holds_abs1_XFER_lbl] >>
METIS_TAC [abs_rel_holds_abs1_tau_spi, abs_rel_holds_abs1_tau_dr, 
abs_rel_holds_abs1_tau_comb]);

val weak_bisim_abs0_abs1 = store_thm("weak_bisim_abs0_abs1",
``weak_bisim abs_rel ds_abs0_tr ds_abs1_tr``,
rw [weak_bisim_def, weak_tr_def] >>
METIS_TAC [abs0_weak_simulation, abs1_weak_simulation]);

val _ = export_theory();
