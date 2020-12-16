open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory SPI_return_regsTheory;
open driver_stateTheory driver_relationTheory driver_readTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory board_memTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_RD_RE";

val ref_rel_hold_dr_init_read_req = store_thm("ref_rel_hold_dr_init_read_req",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.state = dr_init_read_req) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 (dr_read dr with dr_last_read_v := SOME v) spi'``,
rw [spi_tr_cases, dr_read_def, dr_read_sysstatus_def, read_SPI_regs_state_def,
read_SPI_regs_value_def, read_SPI_regs_def] >>
cheat);


(* simulation: ds_abs1' exists and holds the ref_rel when driver_tau *)
val abs1_comb_hold_ref_rel_RD_RE = store_thm("abs1_comb_hold_ref_rel_RD_RE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (Read a v) dr') /\ 
(spi_tr spi (Return a v) spi') ==>
(ref_rel ds_abs1 dr' spi') \/
(?ds_abs1'.(ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi'))``,
rw [driver_tr_cases, DR_RD_ENABLE_def] >>
cheat);

val _ = export_theory();
