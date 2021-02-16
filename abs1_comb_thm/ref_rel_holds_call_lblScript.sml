open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open driver_stateTheory driver_relationTheory driver_callTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

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
Cases_on `spi.state` >>
rw [] >>
`(dr.state <> dr_init_idle) /\
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
(dr.state <> dr_xfer_reset_conf)` by rw [] >>
Cases_on `ds_abs1.state` >>
rw []);

(* If dr.state = dr_ready, then abs1.state = abs1_ready according to ref_rel *)
val dr_ready_imply_abs1_ready = store_thm("dr_ready_imply_abs1_ready",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr,spi)) /\ (dr.state = dr_ready) ==>
ds_abs1.state = abs1_ready``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >>
rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
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
(dr.state <> dr_xfer_reset_conf)` by rw [] >>
Cases_on `ds_abs1.state` >>
rw []);

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
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def],
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []]);

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
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []]);

val _ = export_theory();
