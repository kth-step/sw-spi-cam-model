open HolKernel bossLib boolLib Parse wordsLib;
open SPI_stateTheory SPI_relationTheory SPI_tauTheory SPI_update_regsTheory SPI_return_regsTheory driver_stateTheory driver_relationTheory driver_callTheory driver_writeTheory driver_readTheory driver_checkTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory weak_bisimulationTheory board_memTheory;

val _ = new_theory "ref_rel_holds_call_lbl";

(* lemmas for call labels *)
(* If dr.state = dr_init_pre, then abs1.state = init_pre according to ref_rel *)
val dr_init_pre_imply_abs1_init_pre = store_thm("dr_init_pre_imply_abs1_init_pre",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_pre) ==>
ds_abs1.state = abs1_init_pre``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_ready) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* If dr.state = dr_ready, then abs1.state = abs1_ready according to ref_rel *)
val dr_ready_imply_abs1_ready = store_thm("dr_ready_imply_abs1_ready",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr,spi)) /\ (dr.state = dr_ready) ==>
ds_abs1.state = abs1_ready``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* If dr.state = dr_rx_sendback, then abs1.state = abs1_rx_reset according to ref_rel *)
val dr_rx_sendback_imply_abs1_rx_reset = store_thm("dr_rx_sendback_imply_abs1_rx_reset",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr,spi)) /\ (dr.state = dr_rx_sendback) ==>
ds_abs1.state = abs1_rx_reset``,
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
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* If dr.state = dr_xfer_sendback, then abs1.state = abs1_xfer_reset according to ref_rel *)
val dr_xfer_sendback_imply_abs1_xfer_reset = store_thm("dr_xfer_sendback_imply_abs1_xfer_reset",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr,spi)) /\ (dr.state = dr_xfer_sendback) ==>
ds_abs1.state = abs1_xfer_reset``,
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
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_reset_conf)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exits for call_init label *)
val comb_abs1_hold_ref_rel_call_init = store_thm("comb_abs1_hold_ref_rel_call_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dr':driver_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr call_init dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 call_init ds_abs1') /\ (ref_rel ds_abs1' (dr', spi))``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[ (* abs1_init_pre *)
METIS_TAC [dr_init_pre_imply_abs1_init_pre],
(* ref_rel ds_abs1' dr' spi*)
`ds_abs1.state = abs1_init_pre` by METIS_TAC [dr_init_pre_imply_abs1_init_pre] >>
rw [call_init_ds_abs1_def, call_init_dr_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_ready *)
METIS_TAC [dr_ready_imply_abs1_ready],
(* ref_rel when abs1_init_done *)
`ds_abs1.state = abs1_ready` by METIS_TAC [dr_ready_imply_abs1_ready] >>
rw [call_init_ds_abs1_def, call_init_dr_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);

(* (dr',spi') exists for call_init label *)
val abs1_comb_hold_ref_rel_call_init = store_thm("abs1_comb_hold_ref_rel_call_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 call_init ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) call_init (dr', spi')) /\
(ref_rel ds_abs1' (dr', spi'))``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >> rw [],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >> rw []]);

(* ds_abs1' exists for call_tx label *)
val comb_abs1_hold_ref_rel_call_tx = store_thm("comb_abs1_hold_ref_rel_call_tx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (dr':driver_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (call_tx buffer) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') /\ (ref_rel ds_abs1' (dr', spi))``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC [dr_ready_imply_abs1_ready],
(* check the ref_rel *)
`ds_abs1.state = abs1_ready` by METIS_TAC [dr_ready_imply_abs1_ready] >>
rw [call_tx_ds_abs1_def, call_tx_dr_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);

(* (dr',spi') exists for call_tx label *)
val abs1_comb_hold_ref_rel_call_tx = store_thm("abs1_comb_hold_ref_rel_call_tx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) (call_tx buffer) (dr', spi')) /\
(ref_rel ds_abs1' (dr', spi'))``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_tx_ds_abs1_def, call_tx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []]);

(* bisimulation: ds_abs1' exists for call_rx label *)
val comb_abs1_hold_ref_rel_call_rx = store_thm("comb_abs1_hold_ref_rel_call_rx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (length: num) (dr':driver_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (call_rx length) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1') /\ (ref_rel ds_abs1' (dr', spi))``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC [dr_ready_imply_abs1_ready],
(* check the ref_rel *)
`ds_abs1.state = abs1_ready` by METIS_TAC[dr_ready_imply_abs1_ready] >>
rw [call_rx_ds_abs1_def, call_rx_dr_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);

(* bisimulation: (ds',spi') exists for call_rx label *)
val abs1_comb_hold_ref_rel_call_rx = store_thm("abs1_comb_hold_ref_rel_call_rx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (length: num) (dr':driver_state) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) (call_rx length) (dr', spi')) /\ 
(ref_rel ds_abs1' (dr', spi'))``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_rx_ds_abs1_def, call_rx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []]); 

(* bisimulation: ds_abs1' exists for call_xfer label *)
val comb_abs1_hold_ref_rel_call_xfer = store_thm("comb_abs1_hold_ref_rel_call_xfer",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (dr':driver_state) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (call_xfer buffer) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') /\ 
(ref_rel ds_abs1' (dr', spi))``,
rw [driver_tr_cases, ds_abs1_tr_cases] >-
((* check the state *)
METIS_TAC [dr_ready_imply_abs1_ready]) >>
(* check the ref_rel *)
`ds_abs1.state = abs1_ready` by METIS_TAC [dr_ready_imply_abs1_ready] >>
rw [call_xfer_ds_abs1_def, call_xfer_dr_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* bisimulation: (dr',spi') exists for call_xfer label *)
val abs1_comb_hold_ref_rel_call_xfer = store_thm("abs1_comb_hold_ref_rel_call_xfer",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) (call_xfer buffer) (dr', spi')) /\
(ref_rel ds_abs1' (dr', spi'))``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_xfer_ds_abs1_def, call_xfer_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >> rw []]);

(* bisimulation: ds_abs1' exists for call_back label *)
val comb_abs1_hold_ref_rel_call_back = store_thm("comb_abs1_hold_ref_rel_call_back",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (dr':driver_state) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (call_back buffer) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_back buffer) ds_abs1') /\ 
(ref_rel ds_abs1' (dr', spi))``,
rw [driver_tr_cases,call_back_dr_data_def,call_back_dr_state_def,call_back_dr_def] >-
(`ds_abs1.state = abs1_rx_reset` by METIS_TAC [dr_rx_sendback_imply_abs1_rx_reset] >>
 rw [ds_abs1_tr_cases,call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,
 call_back_ds_abs1_def] >>
 fs [ref_rel_def,IS_STATE_REL_def] >>
 Cases_on `dr.state` >> rw []) >>
`ds_abs1.state = abs1_xfer_reset` by METIS_TAC [dr_xfer_sendback_imply_abs1_xfer_reset] >>
rw [ds_abs1_tr_cases,call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,
call_back_ds_abs1_def] >>
fs [ref_rel_def,IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw []);

(* bisimulation: (dr',spi') exists for call_back label *)
val abs1_comb_hold_ref_rel_call_back = store_thm("abs1_comb_hold_ref_rel_call_back",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list) (ds_abs1':ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_tr ds_abs1 (call_back buffer) ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) (call_back buffer) (dr',spi')) /\
(ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) (call_back buffer) (dr',spi')) /\ 
(ref_rel ds_abs1' (dr',spi')))``,
rw [ds_abs1_tr_cases,call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,
call_back_ds_abs1_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >-
(`(dr.state = dr_rx_sendback /\ spi.state = spi_ready) \/
  (dr.state = dr_rx_reset_conf /\ spi.state = rx_channel_disabled) \/
  (dr.state = dr_rx_read_conf /\ spi.state = rx_channel_disabled) \/
  (dr.state = dr_rx_issue_disable /\ spi.state = rx_data_ready)` by fs [IS_STATE_REL_def] >|[
  (* dr_rx_sendback and spi_ready*)
  DISJ1_TAC >>
  rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
  call_back_dr_def]  >>
  fs [ref_rel_def,IS_STATE_REL_def],
  (* dr_rx_reset_conf and rx_channel_disabled *)
  DISJ2_TAC >>
  Q.EXISTS_TAC `SUC 0:num` >> 
  fs [n_tau_tr_def,local_tr_cases, driver_tr_cases, spi_tr_cases,DR_TAU_ENABLE_def, 
  SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, dr_write_state_def, 
  dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_rx_def] >>
  `dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
  `~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)`
    by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
        FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  `spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
  `(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE`
  by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  `(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM`
  by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
  SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def,
  write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
  call_back_dr_def]  >>
  fs [ref_rel_def,IS_STATE_REL_def],
  (* dr_rx_read_conf and rx_channel_disabled *)
  DISJ2_TAC >>
  Q.EXISTS_TAC `SUC 1:num` >>
  rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def,
  SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >> 
  `dr_read dr = dr with <|state := dr_rx_reset_conf;
   dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
  `(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
   (read_SPI_regs_state SPI0_CH0CONF spi = spi)`
  by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
  SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
  SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> 
  fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
  dr_write_def, dr_write_ch0conf_rx_def] >>
  `~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)`    
  by (fs [build_CH0CONF_def,ch0conf_changed_def] >>       
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  `spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
  `(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
  spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  `(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
   spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_rx_def, 
  SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
  SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
  call_back_dr_def]  >>
  fs [ref_rel_def,IS_STATE_REL_def],
  (* dr_rx_issue_disable and rx_data_ready *)                              
  DISJ2_TAC >>                                  
  Q.EXISTS_TAC `SUC 2:num` >>
  rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def,
      SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
  `(dr_write_state dr = dr with state := dr_rx_read_conf) /\
  (dr_write_address dr = SOME SPI0_CH0CTRL) /\
  (dr_write_value dr = SOME (0w:word32))`
  by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def,
  dr_write_ch0ctrl_def] >> fs [] >>
  `write_SPI_regs SPI0_CH0CTRL 0w spi =
  spi with <|regs := spi.regs with CH0CTRL := 0w;
             state := rx_channel_disabled|>`
  by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
  SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
  `dr_read (dr with state := dr_rx_read_conf) = dr with <|state := dr_rx_reset_conf; 
  dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >> 
  `(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := rx_channel_disabled;
  regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
  (read_SPI_regs_state SPI0_CH0CONF (spi with <|state := rx_channel_disabled;
  regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := rx_channel_disabled;
  regs := spi.regs with CH0CTRL := 0w |>))`
  by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
  SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
  SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
  rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
  dr_write_def, dr_write_ch0conf_rx_def] >>
  `~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
  (spi with <|state := rx_channel_disabled;
  regs := spi.regs with CH0CTRL := 0w|>))` 
  by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  `spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
  `(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
  spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  `(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
  spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
  rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_rx_def, 
  SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
  SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
  FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
  rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
  call_back_dr_def]  >>
  fs [ref_rel_def,IS_STATE_REL_def]]) >>
`(dr.state = dr_xfer_sendback /\ spi.state = spi_ready) \/
(dr.state = dr_xfer_reset_conf /\ spi.state = xfer_channel_disabled) \/
(dr.state = dr_xfer_read_conf /\ spi.state = xfer_channel_disabled) \/
(dr.state = dr_xfer_issue_disable /\ spi.state = xfer_ready_for_trans)` by fs [IS_STATE_REL_def] >|[
(* dr_xfer_sendback and spi_ready *)
DISJ1_TAC >>
rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
call_back_dr_def]  >>
fs [ref_rel_def,IS_STATE_REL_def],
(* dr_xfer_reset and xfer_channel_disabled *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0:num` >> 
fs [n_tau_tr_def,local_tr_cases, driver_tr_cases, spi_tr_cases,DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, dr_write_state_def,
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_xfer_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def,
write_CH0CONF_comb_def, write_CH0CONF_xfer_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
call_back_dr_def]  >>
fs [ref_rel_def,IS_STATE_REL_def],   
(* dr_xfer_read_conf and xfer_channel_disabled *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def,n_tau_tr_SUC,local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <|state := dr_xfer_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF spi = spi)`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> 
fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_xfer_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_xfer_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
call_back_dr_def]  >>
fs [ref_rel_def,IS_STATE_REL_def],
(* dr_xfer_issue_disable and xfer_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 2:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`(dr_write_state dr = dr with state := dr_xfer_read_conf) /\
(dr_write_address dr = SOME SPI0_CH0CTRL) /\
(dr_write_value dr = SOME (0w:word32))` 
by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def, 
dr_write_ch0ctrl_def] >> fs [] >>
`write_SPI_regs SPI0_CH0CTRL 0w spi = 
spi with <|regs := spi.regs with CH0CTRL := 0w;
state := xfer_channel_disabled|>` 
by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
`dr_read (dr with state := dr_xfer_read_conf) = dr with <|state := dr_xfer_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := xfer_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF (spi with <|state := xfer_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := xfer_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>))`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_xfer_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
(spi with <|state := xfer_channel_disabled;
regs := spi.regs with CH0CTRL := 0w|>))` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_xfer_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [local_tr_cases,driver_tr_cases,call_back_dr_state_def,call_back_dr_data_def,
call_back_dr_def]  >>
fs [ref_rel_def,IS_STATE_REL_def]]);  
         
val _ = export_theory();
