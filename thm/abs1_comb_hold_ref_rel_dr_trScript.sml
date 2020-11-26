open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory driver_checkTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;


val _ = new_theory "abs1_comb_hold_ref_rel_spi_tr";


(* bi-simulation: ds_abs1' exists and holds the ref_rel when driver_tau *)
val abs1_comb_hold_ref_rel_driver_tr = store_thm("abs1_comb_hold_ref_rel_driver_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr tau dr') ==>
(ref_rel ds_abs1 dr' spi) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi))``,
rw [driver_tr_cases, dr_check_def] >>
rw [dr_check_sysstatus_def] >>
cheat);


val _ = export_theory();
