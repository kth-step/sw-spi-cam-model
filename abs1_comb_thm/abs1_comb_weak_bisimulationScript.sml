open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory weak_bisimulationTheory driver_stateTheory driver_relationTheory ds_abs1_stateTheory ref_relTheory ds_abs1_relTheory ref_rel_holds_call_lblTheory ref_rel_holds_trans_lblTheory comb_abs1_hold_ref_rel_spi_trTheory comb_abs1_hold_ref_rel_dr_trTheory comb_abs1_hold_ref_rel_RD_RETheory comb_abs1_hold_ref_rel_WR_UPTheory abs1_comb_hold_ref_rel_tau_spiTheory abs1_comb_hold_ref_rel_tau_drTheory abs1_comb_hold_ref_rel_tau_combTheory;

val _ = new_theory "abs1_comb_weak_bisimulation";

(* if (dr,spi) -> (dr', spi'), ds_abs1 matches *)
(* simulation: ds_abs1' exists when lbl is not tau *)
val comb_abs1_weak_simulation_lbl_not_tau = store_thm("comb_abs1_weak_simulation_lbl_not_tau",
``!spi dr ds_abs1 lbl dr' spi'.
(ref_rel ds_abs1 (dr, spi)) /\ (local_tr (dr, spi) lbl (dr', spi')) ==>
(lbl <> tau ==> 
?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' (dr', spi')))``,
rw [local_tr_cases] >>
METIS_TAC [comb_abs1_hold_ref_rel_call_init,comb_abs1_hold_ref_rel_call_tx,
comb_abs1_hold_ref_rel_call_rx,comb_abs1_hold_ref_rel_call_xfer,
comb_abs1_hold_ref_rel_call_back,comb_abs1_hold_ref_rel_TX,
comb_abs1_hold_ref_rel_RX,comb_abs1_hold_ref_rel_XFER]);

(* simulation: ds_abs1 or ds_abs1' exists for ref_rel holding when lbl is tau *)
val comb_abs1_weak_simulation_tau = store_thm("comb_abs1_weak_simulation_tau",
``!spi dr ds_abs1 dr' spi'.
(ref_rel ds_abs1 (dr, spi)) /\ (local_tr (dr, spi) tau (dr', spi')) ==>
(ref_rel ds_abs1 (dr', spi')) \/ 
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' (dr', spi')))``,
rw [local_tr_cases] >> 
METIS_TAC [comb_abs1_hold_ref_rel_driver_tr, comb_abs1_hold_ref_rel_spi_tr,
comb_abs1_hold_ref_rel_WR_UP, comb_abs1_hold_ref_rel_RD_RE]);

(* simulation: when (dr, spi) performs state transition, ds_abs1 is simulated to (dr,spi). *)
val comb_abs1_weak_simulation = store_thm("comb_abs1_weak_simulation",
``!spi dr ds_abs1 lbl dr' spi'.
(ref_rel ds_abs1 (dr,spi)) /\ (local_tr (dr,spi) lbl (dr',spi')) ==>
(lbl = tau ==>
(?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' (dr',spi'))) \/
(ref_rel ds_abs1 (dr',spi'))) /\
(lbl <> tau ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' (dr',spi')))``,
rw []  >>
METIS_TAC [comb_abs1_weak_simulation_tau, comb_abs1_weak_simulation_lbl_not_tau]);

(* if ds_abs1 -> ds_abs1', (dr,spi) matches *)
(* simulation: (dr', spi') exists when lbl is not tau *)
val abs1_comb_weak_simulation_lbl_not_tau = store_thm("abs1_comb_weak_simulation_lbl_not_tau",
``!spi dr ds_abs1 lbl ds_abs1'.
ref_rel ds_abs1 (dr, spi) /\ ds_abs1_tr ds_abs1 lbl ds_abs1' ==>
lbl <> tau ==>
(?dr' spi'. (local_tr (dr, spi) lbl (dr', spi')) /\ 
(ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr, spi) lbl (dr', spi')) /\
(ref_rel ds_abs1' (dr', spi')))``,
rw [ds_abs1_tr_cases] >>
rw [abs1_comb_hold_ref_rel_TX, abs1_comb_hold_ref_rel_RX, abs1_comb_hold_ref_rel_XFER] >>
METIS_TAC [ds_abs1_tr_cases, abs1_comb_hold_ref_rel_call_init, 
abs1_comb_hold_ref_rel_call_init, abs1_comb_hold_ref_rel_call_tx,
abs1_comb_hold_ref_rel_call_rx, abs1_comb_hold_ref_rel_call_xfer,
abs1_comb_hold_ref_rel_call_back]);

(* simulation: (dr',spi') exists when lbl is tau *)
val abs1_comb_weak_simulation_tau = store_thm("abs1_comb_weak_simulation_tau",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 tau ds_abs1') ==>
(?dr' spi'. (local_tr (dr,spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr, spi) tau (dr', spi')) /\
(ref_rel ds_abs1' (dr', spi')))``,
rw [ds_abs1_tr_cases] >>
METIS_TAC [abs1_comb_hold_ref_rel_tau_spi, abs1_comb_hold_ref_rel_tau_dr,
abs1_comb_hold_ref_rel_tau_comb]);

(* simulation: when ds_abs1 performs state transition, (dr,spi) is simulated to ds_abs1 *)
val abs1_comb_weak_simulation = store_thm("abs1_comb_weak_simulation",
``!spi dr ds_abs1 lbl ds_abs1'.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1_tr ds_abs1 lbl ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) lbl (dr', spi')) /\ (ref_rel ds_abs1' (dr',spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) lbl (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))``,
rw [] >>
Cases_on `lbl = tau` >>
METIS_TAC [abs1_comb_weak_simulation_tau, abs1_comb_weak_simulation_lbl_not_tau]);

(* weak bisimulation: ds_abs1 and (dr,spi) with the ref_rel *)
val weak_bisimulation_abs1_comb = store_thm("weak_bisimulation_abs1_comb",
``weak_bisim ref_rel ds_abs1_tr local_tr``,
rw [weak_bisim_def, weak_tr_def] >>
Cases_on `s2` >-
(METIS_TAC [abs1_comb_weak_simulation]) >>
Cases_on `s2'` >>
METIS_TAC [comb_abs1_weak_simulation]);


val _ = export_theory();
