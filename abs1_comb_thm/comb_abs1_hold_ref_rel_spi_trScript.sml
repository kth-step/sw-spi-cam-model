open HolKernel bossLib boolLib Parse wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory SPI_tauTheory driver_stateTheory driver_relationTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory;

val _ = new_theory "comb_abs1_hold_ref_rel_spi_tr";

(* ref_rel holds for ds_abs1 dr spi' in case of init tau transition *)
val ref_rel_spi_init_tau = store_thm("ref_rel_spi_init_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
ref_rel ds_abs1 (dr, spi) /\ spi.state = init_reset ==>
ref_rel ds_abs1 (dr, spi_tau_operations spi)``,
rw [spi_tau_operations_def, init_reset_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `ds_abs1.state` >> rw [] >> rw [] >>
Cases_on `dr.state` >> rw []);


(* a lemma: TX_TAU_ENABLE spi ==> SPI_ABS1_TX_ENABLE ds_abs1 based on ref_rel *)
val COMB_IMP_ABS1_TX_ENABLE = store_thm("COMB_IMP_ABS1_TX_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ 
(spi.state = tx_channel_enabled \/ spi.state = tx_trans_data \/ spi.state = tx_trans_update) ==>
(SPI_ABS1_TX_ENABLE ds_abs1)``,
rw [SPI_ABS1_TX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exists when spi.state = tx_channel_enabled *)
val ref_rel_spi_tx_tau_channel_enabled = store_thm("ref_rel_spi_tx_tau_channel_enabled",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = tx_channel_enabled) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
`SPI_ABS1_TX_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_TX_ENABLE] >> rw [] >>
fs [SPI_ABS1_TX_ENABLE_def] >|
[(* abs1_tx_idle *)
rw [spi_abs1_tx_operations_def, spi_abs1_tx_idle_op_def,
spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_data_1 *)
`spi.state = tx_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_data_2 *)
`spi.state = tx_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_update *)
`spi.state = tx_trans_update` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_last_update *)
`spi.state = tx_trans_update` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);

(* ds_abs1' exists when spi.state = tx_trans_data *)
val ref_rel_spi_tx_tau_trans_data = store_thm("ref_rel_spi_tx_tau_trans_data",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = tx_trans_data) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
`SPI_ABS1_TX_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_TX_ENABLE] >> rw [] >>
fs [SPI_ABS1_TX_ENABLE_def] >|
[(* abs1_tx_idle *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [],
(* abs1_tx_data_1 *)
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_1_op_def,
spi_tau_operations_def, tx_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_data_2 *)
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_2_op_def,
spi_tau_operations_def, tx_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_update *)
`spi.state = tx_trans_update` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_last_update *)
`spi.state = tx_trans_update` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);

(* ds_abs1' exists when spi.state = tx_trans_update *)
val ref_rel_spi_tx_tau_trans_update = store_thm("ref_rel_spi_tx_tau_trans_update",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = tx_trans_update) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
`SPI_ABS1_TX_ENABLE ds_abs1` by METIS_TAC[COMB_IMP_ABS1_TX_ENABLE] >> rw [] >>
fs [SPI_ABS1_TX_ENABLE_def] >|
[(* abs1_tx_idle *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [],
(* abs1_tx_data_1 *)
`spi.state = tx_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_data_2 *)
`spi.state = tx_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_tx_update *)
rw [spi_abs1_tx_operations_def, spi_abs1_tx_update_op_def,
spi_tau_operations_def, tx_trans_update_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_last_update *)
rw [spi_abs1_tx_operations_def, spi_abs1_tx_last_update_op_def,
spi_tau_operations_def, tx_trans_update_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);


(* a lemma: RX_TAU_ENABLE spi => SPI_ABS1_RX_ENABLE ds_abs1 based on ref_rel *)
val COMB_IMP_ABS1_RX_ENABLE = store_thm("COMB_IMP_ABS1_RX_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ 
(spi.state = rx_channel_enabled \/ spi.state = rx_update_RX0) ==>
(SPI_ABS1_RX_ENABLE ds_abs1)``,
rw [SPI_ABS1_RX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exists when spi.state = rx_channel_enabled *)
val ref_rel_spi_rx_tau_channel_enabled = store_thm("ref_rel_spi_rx_tau_channel_enabled",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = rx_channel_enabled) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
`SPI_ABS1_RX_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_RX_ENABLE] >> rw [] >>
fs [SPI_ABS1_RX_ENABLE_def] >|
[(* abs1_rx_idle *)
rw [spi_abs1_rx_operations_def, spi_abs1_rx_idle_op_def,
spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_rx_update *)
`spi.state = rx_update_RX0` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_rx_next *)
`spi.state = rx_update_RX0` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);

(* ds_abs1' exists when spi.state = rx_update_RX0 *)
val ref_rel_spi_rx_tau_update_RX0 = store_thm("ref_rel_spi_rx_tau_update_RX0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = rx_update_RX0) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
`SPI_ABS1_RX_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_RX_ENABLE] >> rw [] >>
fs [SPI_ABS1_RX_ENABLE_def] >|
[(* abs1_rx_idle *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [],
(* abs1_rx_update *)
rw [spi_abs1_rx_operations_def, spi_abs1_rx_update_op_def,
spi_tau_operations_def, rx_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* abs1_rx_next *)
rw [spi_abs1_rx_operations_def, spi_abs1_rx_next_op_def,
spi_tau_operations_def, rx_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]);

(* a lemma: XFER_TAU_ENABLE spi => SPI_ABS1_XFER_ENABLE ds_abs1 based on ref_rel *)
val COMB_IMP_ABS1_XFER_ENABLE = store_thm("COMB_IMP_ABS1_XFER_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = xfer_channel_enabled \/
spi.state = xfer_trans_data \/ spi.state = xfer_update_RX0) ==>
(SPI_ABS1_XFER_ENABLE ds_abs1)``,
rw [SPI_ABS1_XFER_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exists when spi.state = xfer_channel_enabled *)
val ref_rel_spi_xfer_tau_channel_enabled = store_thm("ref_rel_spi_xfer_tau_channel_enabled",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = xfer_channel_enabled) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
`SPI_ABS1_XFER_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_XFER_ENABLE] >> rw [] >>
fs [SPI_ABS1_XFER_ENABLE_def] >|
[(* abs1_xfer_idle *)
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_idle_op_def,
spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_xfer_data *)
`spi.state = xfer_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_xfer_update *)
`spi.state = xfer_update_RX0` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);

(* ds_abs1' exists when spi.state = xfer_trans_data *)
val ref_rel_spi_xfer_tau_trans_data = store_thm("ref_rel_spi_xfer_tau_trans_data",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = xfer_trans_data) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
`SPI_ABS1_XFER_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_XFER_ENABLE] >>
rw [] >>
fs [SPI_ABS1_XFER_ENABLE_def] >|
[(* abs1_xfer_idle *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [],
(* abs1_xfer_data *)
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_data_op_def,
spi_tau_operations_def, xfer_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_xfer_update *)
`spi.state = xfer_update_RX0` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);

(* ds_abs1' exists when spi.state = xfer_update_RX0 *)
val ref_rel_spi_xfer_tau_update_RX0 = store_thm("ref_rel_spi_xfer_tau_update_RX0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = xfer_update_RX0) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' (dr, (spi_tau_operations spi)))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
`SPI_ABS1_XFER_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_XFER_ENABLE] >>
rw [] >>
fs [SPI_ABS1_XFER_ENABLE_def] >|
[(* abs1_xfer_idle *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
Cases_on `spi.state` >> rw [] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [],
(* abs1_xfer_data *)
`spi.state = xfer_trans_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
(* abs1_xfer_update *)
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_update_op_def,
spi_tau_operations_def, xfer_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]);

(* simulation: ds_abs1' exists and holds the ref_rel when spi_tau *)
val comb_abs1_hold_ref_rel_spi_tr = store_thm("comb_abs1_hold_ref_rel_spi_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi_tr spi tau spi') ==>
(ref_rel ds_abs1 (dr, spi')) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' (dr, spi')))``,
rw [spi_tr_cases] >>
fs [SPI_TAU_ENABLE_def] >>
rw [ref_rel_spi_init_tau, ref_rel_spi_tx_tau_channel_enabled,
ref_rel_spi_tx_tau_trans_data, ref_rel_spi_tx_tau_trans_update,
ref_rel_spi_rx_tau_channel_enabled, ref_rel_spi_rx_tau_update_RX0, 
ref_rel_spi_xfer_tau_channel_enabled, ref_rel_spi_xfer_tau_trans_data, 
ref_rel_spi_xfer_tau_update_RX0]);

val _ = export_theory();
