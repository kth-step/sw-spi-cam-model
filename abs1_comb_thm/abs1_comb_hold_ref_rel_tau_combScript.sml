open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_tau_comb";

(* simulation: (dr',spi') exists and holds the ref_rel when ds_abs1 has tau_comb transitions *)
val abs1_comb_hold_ref_rel_tau_comb = store_thm("abs1_comb_hold_ref_rel_tau_comb",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ (ref_rel ds_ab1' (dr',spi')))``,
cheat);

val _ = export_theory();
