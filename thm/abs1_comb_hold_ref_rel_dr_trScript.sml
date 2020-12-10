open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_relationTheory driver_checkTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;


val _ = new_theory "abs1_comb_hold_ref_rel_spi_tr";

val ref_rel_check_SYSSTATUS = store_thm("ref_rel_check_SYSSTATUS",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_last_read_ad = SOME SPI0_SYSSTATUS) /\
(dr.dr_last_read_v = SOME v) /\ (INIT_CHECK_ENABLE dr) ==>
ref_rel ds_abs1 (dr_check_sysstatus dr v) spi``,
rw [dr_check_sysstatus_def, INIT_CHECK_ENABLE_def] >|
[FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [] >>
Cases_on `spi.init.state` >>
rw [] >>
FULL_SIMP_TAC (std_ss++WORD_ss) [],
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

val ref_rel_check_CH0STAT_TX = store_thm("ref_rel_check_CH0STAT_TX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (TX_CHECK_ENABLE dr) ==>
(ref_rel ds_abs1 (dr_check_ch0stat dr v) spi)``,
rw [TX_CHECK_ENABLE_def, dr_check_ch0stat_def] >|
[rw [dr_check_tx_ch0stat_def] >|
[FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [] >>
cheat,
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []],

rw [dr_check_tx_ch0stat_def] >|
[FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [] >>
cheat,
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]]);

(* bi-simulation: ds_abs1' exists and holds the ref_rel when driver_tau *)
val abs1_comb_hold_ref_rel_driver_tr = store_thm("abs1_comb_hold_ref_rel_driver_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr tau dr') ==>
(ref_rel ds_abs1 dr' spi) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr' spi))``,
rw [driver_tr_cases] >|
[
FULL_SIMP_TAC std_ss [dr_tx_syn_tr_cases] >>
rw [] >>
cheat,
cheat,
cheat,

rw [dr_check_def] >>
rw [ref_rel_check_SYSSTATUS]
rw [ref_rel_check_CH0STAT_TX]
rw [ref_rel_check_CH0STAT_RX]


]);


val _ = export_theory();
