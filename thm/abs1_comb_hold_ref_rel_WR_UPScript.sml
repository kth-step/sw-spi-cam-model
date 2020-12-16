open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_WR_UP";


(* simulation: ds_abs1' exists and holds the ref_rel when driver_tau *)
val abs1_comb_hold_ref_rel_WR_UP = store_thm("abs1_comb_hold_ref_rel_WR_UP",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (Write a v) dr') /\ 
(spi_tr spi (Update a v) spi') ==>
(ref_rel ds_abs1 dr' spi') \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
cheat);

val _ = export_theory();
