open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory;
open ref_relTheory;
open ds_abs1_relTheory;
open abs1_comb_hold_ref_rel_call_lblTheory;
open abs1_comb_hold_ref_rel_trans_lblTheory;

val _ = new_theory "abs1_comb_hold_ref_rel";

(* bi-simulation: ds_abs1' exists when lbl is not tau *)
val abs1_comb_hold_ref_rel_not_tau_lbl = store_thm("abs1_comb_hold_ref_rel_not_tau_lbl",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (lbl:global_lbl_type).
(ref_rel ds_abs1 dr spi) /\ (local_tr (dr, spi) lbl (dr', spi')) ==>
(lbl <> tau ==> ?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
rw [local_tr_cases] >|
[METIS_TAC [abs1_comb_hold_ref_rel_call_init],
METIS_TAC [abs1_comb_hold_ref_rel_call_tx],
METIS_TAC [abs1_comb_hold_ref_rel_call_rx],
METIS_TAC [abs1_comb_hold_ref_rel_call_xfer],
METIS_TAC [abs1_comb_hold_ref_rel_TX],
METIS_TAC [abs1_comb_hold_ref_rel_RX],
METIS_TAC [abs1_comb_hold_ref_rel_XFER]]);

val abs1_comb_hold_ref_rel_driver_tr = store_thm("abs1_comb_hold_ref_rel_driver_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr tau dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
cheat);

val abs1_comb_hold_ref_rel_spi_tr = store_thm("abs1_comb_hold_ref_rel_spi_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi tau spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
cheat);

val abs1_comb_hold_ref_rel_WR_UP = store_thm("abs1_comb_hold_ref_rel_WR_UP",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (Write a v) dr') /\ 
(spi_tr spi (Update a v) spi') ==>
(ref_rel ds_abs1 dr' spi') \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
cheat);

val abs1_comb_hold_ref_rel_RD_RE = store_thm("abs1_comb_hold_ref_rel_RD_RE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (Read a v) dr') /\ 
(spi_tr spi (Return a v) spi') ==>
(ref_rel ds_abs1 dr' spi')``,
cheat);

(* bi-simulation: ds_abs1 or ds_abs1' exists when lbl is tau *)
val abs1_comb_hold_ref_rel_tau = store_thm("abs1_comb_hold_ref_rel_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (local_tr (dr, spi) tau (dr', spi')) ==>
(ref_rel ds_abs1 dr' spi') \/ (?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
rw [local_tr_cases] >|
[METIS_TAC [abs1_comb_hold_ref_rel_driver_tr],
METIS_TAC [abs1_comb_hold_ref_rel_spi_tr],
METIS_TAC [abs1_comb_hold_ref_rel_WR_UP],
METIS_TAC [abs1_comb_hold_ref_rel_RD_RE]]);

(* bi-simulation ds_abs1 *)
val abs1_comb_hold_ref_rel = store_thm("abs1_comb_hold_ref_rel",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (lbl:global_lbl_type).
(ref_rel ds_abs1 dr spi) /\ (local_tr (dr, spi) lbl (dr', spi')) ==>
(lbl <> tau ==> ?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' dr' spi')) /\
(lbl = tau ==> (ref_rel ds_abs1 dr' spi') \/ (?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') \/ (ref_rel ds_abs1' dr' spi')))``,
cheat);

(* bi-simulation: (dr', spi') exists when lbl is not tau *)
val comb_abs1_hold_ref_rel_not_tau_lbl = store_thm("comb_abs1_hold_ref_rel_not_tau_lbl",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (lbl:global_lbl_type).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 lbl ds_abs1') ==>
(lbl <> tau ==> ?dr' spi'. (local_tr (dr, spi) lbl (dr', spi')) /\ (ref_rel ds_abs1' dr' spi'))``,
rw [ds_abs1_tr_cases] >|
[METIS_TAC [ds_abs1_tr_cases, comb_abs1_hold_ref_rel_call_init], 
METIS_TAC [ds_abs1_tr_cases, comb_abs1_hold_ref_rel_call_tx],
METIS_TAC [ds_abs1_tr_cases, comb_abs1_hold_ref_rel_call_rx], 
METIS_TAC [ds_abs1_tr_cases, comb_abs1_hold_ref_rel_call_xfer],
rw [comb_abs1_hold_ref_rel_TX],
rw [comb_abs1_hold_ref_rel_RX],
rw [comb_abs1_hold_ref_rel_XFER]]);

val comb_abs1_hold_ref_rel_tau_spi = store_thm("comb_abs1_hold_ref_rel_tau_spi",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_spi_tr ds_abs1 tau_spi ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' dr' spi')``,
cheat);

val comb_abs1_hold_ref_rel_tau_dr = store_thm("comb_abs1_hold_ref_rel_tau_spi",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_dr_tr ds_abs1 tau_dr ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' dr' spi')``,
cheat);

val comb_abs1_hold_ref_rel_tau_comb = store_thm("comb_abs1_hold_ref_rel_tau_comb",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' dr' spi')``,
cheat);

(* bi-simulation (dr',spi') when lbl is tau *)
val comb_abs1_hold_ref_rel_tau = store_thm("comb_abs1_hold_ref_rel_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 tau ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' dr' spi')``,
rw [ds_abs1_tr_cases] >|
[METIS_TAC [comb_abs1_hold_ref_rel_tau_spi],
METIS_TAC [comb_abs1_hold_ref_rel_tau_dr],
METIS_TAC [comb_abs1_hold_ref_rel_tau_comb]]);

(* bi-simulation (dr, spi') *)
val comb_abs1_hold_ref_rel = store_thm("comb_abs1_hold_ref_rel",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (lbl:global_lbl_type).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 lbl ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) lbl (dr', spi')) /\ (ref_rel ds_abs1' dr' spi'))``,
cheat);


val _ = export_theory();
