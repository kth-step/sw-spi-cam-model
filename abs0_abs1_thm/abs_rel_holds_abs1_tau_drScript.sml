open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory ds_abs0_relTheory abs_relTheory ds_abs0_initTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_xferTheory ds_abs0_tauTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_abs1_tau_dr";

(* abs_rel_holds for abs1 rx automaton tau_dr transition *)
val abs_rel_holds_abs1_tau_dr_rx = store_thm("abs_rel_holds_abs1_tau_dr_rx",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (DRIVER_ABS1_RX_ENABLE ds_abs1) ==>
?ds_abs0'. ds_abs0_tr ds_abs0 tau ds_abs0' /\ 
abs_rel ds_abs0' (driver_abs1_rx_operations ds_abs1)``,
rw [DRIVER_ABS1_RX_ENABLE_def, driver_abs1_rx_operations_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >|
[(* abs1_rx_ready *)
`ds_abs0.state = abs0_rx_update` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [driver_abs1_rx_ready_op_def] >|
[`ds_abs0.ds_abs0_rx.rx_left_length > 0` by METIS_TAC [abs_rel_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_update_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
`~(ds_abs0.ds_abs0_rx.rx_left_length > 0)` by METIS_TAC [abs_rel_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_update_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* abs1_rx_fetch_data *)
`ds_abs0.state = abs0_rx_reading` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [driver_abs1_rx_fetch_data_op_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_reading_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_rx_next *)
`ds_abs0.state = abs0_rx_next` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [driver_abs1_rx_next_op_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_next_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_rx_next_ready *)
`ds_abs0.state = abs0_rx_next` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [driver_abs1_rx_next_ready_op_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_next_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel_holds for abs1 xfer automaton tau_dr transition *)
val abs_rel_holds_abs1_tau_dr_xfer = store_thm("abs_rel_holds_abs1_tau_dr_xfer",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (DRIVER_ABS1_XFER_ENABLE ds_abs1) ==>
?ds_abs0'. ds_abs0_tr ds_abs0 tau ds_abs0' /\ 
abs_rel ds_abs0' (driver_abs1_xfer_operations ds_abs1)``,
rw [DRIVER_ABS1_XFER_ENABLE_def, driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_xfer_done` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[`ds_abs1.state <> abs1_xfer_data /\ ds_abs1.state <> abs1_xfer_exchange` by rw [] >>
`ds_abs0.ds_abs0_xfer.xfer_cur_length < LENGTH ds_abs0.ds_abs0_xfer.xfer_dataOUT_buffer` by METIS_TAC [abs_rel_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_xfer_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
`ds_abs1.state <> abs1_xfer_data /\ ds_abs1.state <> abs1_xfer_exchange` by rw [] >>
`~ (ds_abs0.ds_abs0_xfer.xfer_cur_length < LENGTH ds_abs0.ds_abs0_xfer.xfer_dataOUT_buffer)` by METIS_TAC [abs_rel_def] >>
rw [ds_abs0_tr_cases, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_xfer_tau_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds when ds_abs1 peforms tau_dr *)
val abs_rel_holds_abs1_tau_dr = store_thm("abs_rel_holds_abs1_tau_dr",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (ds_abs1':ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1_dr_tr ds_abs1 tau_dr ds_abs1') ==>
(abs_rel ds_abs0 ds_abs1') \/
(?ds_abs0'. ds_abs0_tr ds_abs0 tau ds_abs0' /\ abs_rel ds_abs0' ds_abs1')``,
rw [ds_abs1_dr_tr_cases] >>
rw [abs_rel_holds_abs1_tau_dr_rx, abs_rel_holds_abs1_tau_dr_xfer]);

val _ = export_theory();
