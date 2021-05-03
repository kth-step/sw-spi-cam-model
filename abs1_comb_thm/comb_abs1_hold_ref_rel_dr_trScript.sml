open HolKernel bossLib boolLib Parse wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory driver_stateTheory driver_relationTheory driver_checkTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "comb_abs1_hold_ref_rel_dr_tr";

(* driver tau transition to check the SYSSTATUS register *)
val ref_rel_check_sysstatus = store_thm("ref_rel_check_sysstatus",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_SYSSTATUS) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_init_check_rep) ==>
ref_rel ds_abs1 ((dr_check_sysstatus dr v), spi)``,
rw [dr_check_sysstatus_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
FULL_SIMP_TAC (std_ss++WORD_ss) []);

(* driver tau transition to check TXS Bit for tx automaton *)
val ref_rel_check_tx_txs = store_thm("ref_rel_check_tx_txs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_tx_check_txs) ==>
(ref_rel ds_abs1 ((dr_check_tx_ch0stat dr v), spi))``,
rw [dr_check_tx_ch0stat_def] >|
[fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >> 
FULL_SIMP_TAC (std_ss++WORD_ss) [],
fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [],
Cases_on `(1 >< 1) v: word1` >>
FULL_SIMP_TAC (arith_ss ++ WORD_ss) [] >>
Cases_on `n` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) [] >>
Cases_on `n'` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) []]);

(* driver tau transition to check EOT Bit for tx automaton *)
val ref_rel_check_tx_eot = store_thm("ref_rel_check_tx_eot",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_tx_check_eot) ==>
(ref_rel ds_abs1 ((dr_check_tx_ch0stat dr v), spi))``,
rw [dr_check_tx_ch0stat_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []);

(* driver tau transition to check RXS Bit for rx automaton *)
val ref_rel_check_rx_rxs = store_thm("ref_rel_check_rx_rxs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_rx_check_rxs) ==>
(ref_rel ds_abs1 ((dr_check_rx_ch0stat dr v), spi)) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' ((dr_check_rx_ch0stat dr v), spi)))``,
rw [dr_check_rx_ch0stat_def] >|
[(* RXS = 1w /\ left_length > 0 *)
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
fs [ref_rel_def] >>
DISJ2_TAC >>
`ds_abs1.ds_abs1_rx.rx_left_length > 0` by fs [ref_rel_def] >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def] >>
fs [IS_STATE_REL_def],
(* RXS = 1w /\ left_length < 0 *)
`~ (dr.dr_rx.rx_left_length > 0)` by fs [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
fs [ref_rel_def] >>
DISJ2_TAC >>
`~(ds_abs1.ds_abs1_rx.rx_left_length > 0)` by fs [ref_rel_def] >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def] >>
fs [IS_STATE_REL_def],
(* RXS = 0w *)
fs[ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []]);


(* lemma:dr.state = dr_rx_fetch_data -> 
   ds_abs1 is able to perform tau_driver operations, according to ref_rel *)
val dr_rx_fetch_data_imply_driver_abs1_rx_enable = 
store_thm ("dr_rx_fetch_data_imply_driver_abs1_rx_enable",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_fetch_data) ==>
DRIVER_ABS1_RX_ENABLE ds_abs1``,
rw [DRIVER_ABS1_RX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_ready) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* driver tau transition to check RX0 register for rx automaton *)
val ref_rel_check_rx_rx0 = store_thm("ref_rel_check_rx_rx0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_RX0) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_rx_fetch_data) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_check_rx0 dr v), spi))``,
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
`DRIVER_ABS1_RX_ENABLE ds_abs1` by METIS_TAC [dr_rx_fetch_data_imply_driver_abs1_rx_enable] >>
fs [DRIVER_ABS1_RX_ENABLE_def] >>
rw [dr_check_rx0_def, driver_abs1_rx_operations_def, driver_abs1_rx_fetch_data_op_def,
driver_abs1_rx_next_op_def, driver_abs1_rx_next_ready_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw []);

(* driver tau transition to check TXS for xfer automaton *)
val ref_rel_check_xfer_txs = store_thm("ref_rel_check_xfer_txs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_xfer_check_txs) ==>
(ref_rel ds_abs1 ((dr_check_xfer_ch0stat dr v), spi))``,
rw [dr_check_xfer_ch0stat_def] >> 
fs [ref_rel_def, IS_STATE_REL_def] >-
(Cases_on `spi.state` >> rw [] >> 
FULL_SIMP_TAC (std_ss++WORD_ss) []) >>
Cases_on `(1 >< 1) v: word1` >>
FULL_SIMP_TAC (arith_ss ++ WORD_ss) [] >>
Cases_on `n` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) [] >>
Cases_on `n'` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) []);

(* driver tau transition to check RXS for xfer automaton *)
val ref_rel_check_xfer_rxs = store_thm("ref_rel_check_xfer_rxs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_xfer_check_rxs) ==>
(ref_rel ds_abs1 ((dr_check_xfer_ch0stat dr v), spi))``,
rw [dr_check_xfer_ch0stat_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >-
(Cases_on `spi.state` >> rw [] >> 
FULL_SIMP_TAC (std_ss++WORD_ss) []) >>
Cases_on `(0 >< 0) v: word1` >>
FULL_SIMP_TAC (arith_ss ++ WORD_ss) [] >>
Cases_on `n` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) [] >>
Cases_on `n'` >>
FULL_SIMP_TAC (arith_ss++WORD_ss) []);

(* lemma to ensure the ds_abs1.state *)
val dr_xfer_fetch_dataI_imply_abs1_xfer_fetch_data =
store_thm("dr_xfer_fetch_dataI_imply_abs1_xfer_fetch_data",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_fetch_dataI) ==>
ds_abs1.state = abs1_xfer_fetch_data``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_ready) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_sendback) ` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* driver tau transition to check RX0 for xfer automaton *)
val ref_rel_check_xfer_rx0 = store_thm("ref_rel_check_xfer_rx0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.dr_last_read_ad = SOME SPI0_RX0) /\
(dr.dr_last_read_v = SOME v) /\ (dr.state = dr_xfer_fetch_dataI) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' ((dr_check_rx0 dr v), spi))``,
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_XFER_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_xfer_operations ds_abs1`` >>
`ds_abs1.state = abs1_xfer_fetch_data` by METIS_TAC [dr_xfer_fetch_dataI_imply_abs1_xfer_fetch_data] >>
rw [dr_check_rx0_def, driver_abs1_xfer_operations_def] >-
((* not the last byte*)
`ds_abs1.ds_abs1_xfer.xfer_cur_length < (LENGTH (ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer))` by fs [ref_rel_def] >>
rw [driver_abs1_xfer_fetch_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]) >>
(* the last byte*)
`~(ds_abs1.ds_abs1_xfer.xfer_cur_length < (LENGTH (ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer)))` by fs [ref_rel_def] >>
rw [driver_abs1_xfer_fetch_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);


(* simulation: ds_abs1' exists and holds the ref_rel when driver_tau *)
val comb_abs1_hold_ref_rel_driver_tr = store_thm("comb_abs1_hold_ref_rel_driver_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dr':driver_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr tau dr') ==>
(ref_rel ds_abs1 (dr', spi)) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' (dr', spi)))``,
rw [driver_tr_cases] >>
fs [DR_TAU_ENABLE_def, dr_check_def] >>
rw [ref_rel_check_sysstatus, ref_rel_check_tx_txs, ref_rel_check_tx_eot,
ref_rel_check_rx_rxs, ref_rel_check_rx_rx0, ref_rel_check_xfer_txs,
ref_rel_check_xfer_rxs, ref_rel_check_xfer_rx0] >>
fs [ref_rel_def]);

val _ = export_theory();
