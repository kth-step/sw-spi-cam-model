open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory;
open ref_relTheory;
open ds_abs1_relTheory SPI_txTheory ds_abs1_txTheory;
open abs1_comb_hold_ref_rel_call_lblTheory;
open abs1_comb_hold_ref_rel_trans_lblTheory;

val _ = new_theory "abs1_comb_hold_ref_rel";


(* ref_rel holds when lbl is not tau *)
val abs1_comb_hold_ref_rel_not_tau_lbl = store_thm("abs1_comb_hold_ref_rel_not_tau_lbl",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (lbl:global_lbl_type).
(ref_rel ds_abs1 dr spi) /\ (local_tr (dr, spi) lbl (dr', spi')) ==>
(lbl <> tau ==> ?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
rw [local_tr_cases] >|
[METIS_TAC [abs1_comb_hold_ref_rel_call_init],
METIS_TAC [abs1_comb_hold_ref_rel_call_tx],
METIS_TAC [abs1_comb_hold_ref_rel_call_rx],
METIS_TAC [abs1_comb_hold_ref_rel_call_xfer],
METIS_TAC [abs1_comb_hold_ref_rel_TX_lbl],
cheat
);










val _ = export_theory();
