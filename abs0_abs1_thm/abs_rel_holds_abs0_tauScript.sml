open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory weak_bisimulationTheory ds_abs0_relTheory abs_relTheory ds_abs0_tauTheory ds_abs0_rxTheory ds_abs0_xferTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_abs0_tau";

(* abs_rel holds when ds_abs0.state = abs0_rx_update *)
val abs_rel_holds_tau_abs0_rx_update = store_thm("abs_rel_holds_tau_abs0_rx_update",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_rx_update) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1') \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1')``,
rw [abs0_tau_op_def, abs0_rx_update_tau_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_rx_ready \/ ds_abs1.state = abs1_rx_update` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* rx_left_length > 0, abs1_rx_ready *)
`ds_abs1.ds_abs1_rx.rx_left_length > 0` by METIS_TAC [abs_rel_def] >>
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* rx_left_length > 0, abs1_rx_update *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_RX_ENABLE_def, 
ds_abs1_dr_tr_cases, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_rx_operations (spi_abs1_rx_operations ds_abs1)`` >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
`ds_abs1.ds_abs1_rx.rx_left_length > 0` by METIS_TAC [abs_rel_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_update_op_def, 
driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def, DRIVER_ABS1_RX_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* rx_left_length <= 0, abs1_rx_ready *)
`~ (ds_abs1.ds_abs1_rx.rx_left_length > 0)` by METIS_TAC [abs_rel_def] >>
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* rx_left_length <= 0, abs1_rx_update *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_RX_ENABLE_def, 
ds_abs1_dr_tr_cases, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_rx_operations (spi_abs1_rx_operations ds_abs1)`` >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
`~(ds_abs1.ds_abs1_rx.rx_left_length > 0)` by METIS_TAC [abs_rel_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_update_op_def, 
driver_abs1_rx_operations_def, driver_abs1_rx_ready_op_def, DRIVER_ABS1_RX_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds when ds_abs0.state = abs0_rx_reading *)
val abs_rel_holds_tau_abs0_rx_reading = store_thm("abs_rel_holds_tau_abs0_rx_reading",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_rx_reading) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1') \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1')``,
rw [abs0_tau_op_def, abs0_rx_reading_tau_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_rx_read \/ ds_abs1.state = abs1_rx_fetch_data` 
by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_rx_read *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, ds_abs1_dr_tr_cases,
COMB_ABS1_RX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_rx_operations (comb_abs1_rx_operations ds_abs1)`` >>
EXISTS_TAC ``comb_abs1_rx_operations ds_abs1`` >>
rw [comb_abs1_rx_operations_def, comb_abs1_rx_read_op_def,
driver_abs1_rx_operations_def, driver_abs1_rx_fetch_data_op_def, DRIVER_ABS1_RX_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds when ds_abs0.state = abs0_rx_next *)
val abs_rel_holds_tau_abs0_rx_next = store_thm("abs_rel_holds_tau_abs0_rx_next",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_rx_next) ==>
?ds_abs1'. ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1'``,
rw [abs0_tau_op_def, abs0_rx_next_tau_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_rx_next \/ ds_abs1.state = abs1_rx_next_ready` 
by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_RX_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_rx_operations ds_abs1`` >>
rw [driver_abs1_rx_operations_def, driver_abs1_rx_next_op_def, driver_abs1_rx_next_ready_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel_holds when ds_abs0.state = abs0_xfer_done *)
val abs_rel_holds_tau_abs0_xfer_done = store_thm("abs_rel_holds_tau_abs0_xfer_done",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_xfer_done) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1') \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1')``,
rw [abs0_tau_op_def, abs0_xfer_tau_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_xfer_fetch_data \/ ds_abs1.state = abs1_xfer_ready \/
ds_abs1.state = abs1_xfer_update` by METIS_TAC [IS_ABS_STATE_REL_def] >>
`ds_abs0.ds_abs0_xfer.xfer_cur_length = ds_abs1.ds_abs1_xfer.xfer_cur_length` by fs [abs_rel_def] >|
[(* not the last one, abs1_xfer_fetch_data *)
DISJ1_TAC >>
`ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer` 
by METIS_TAC [abs_rel_def] >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_XFER_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_xfer_operations ds_abs1`` >> 
rw [driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_xfer_ready *)
DISJ2_TAC >>
`ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer` 
by METIS_TAC [abs_rel_def] >>
EXISTS_TAC ``SUC 0: num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, ds_abs1_dr_tr_cases,
COMB_ABS1_XFER_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_xfer_operations (comb_abs1_xfer_operations ds_abs1)`` >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_ready_op_def, DRIVER_ABS1_XFER_ENABLE_def, 
driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_xfer_update *)
DISJ2_TAC >>
`ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer` 
by METIS_TAC [abs_rel_def] >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_xfer_operations (comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1)) `` >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
EXISTS_TAC ``comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1)`` >>
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases, ds_abs1_comb_tr_cases, ds_abs1_dr_tr_cases,
COMB_ABS1_XFER_ENABLE_def, SPI_ABS1_XFER_ENABLE_def, DRIVER_ABS1_XFER_ENABLE_def,
spi_abs1_xfer_operations_def, spi_abs1_xfer_update_op_def, comb_abs1_xfer_operations_def,
comb_abs1_xfer_ready_op_def, driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_xfer_fetch_data *)
DISJ1_TAC >>
`~ (ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer)` 
by METIS_TAC [abs_rel_def] >>
rw [ds_abs1_tr_cases, ds_abs1_dr_tr_cases, DRIVER_ABS1_XFER_ENABLE_def] >>
EXISTS_TAC ``driver_abs1_xfer_operations ds_abs1`` >> 
rw [driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_xfer_done *)
DISJ2_TAC >>
`~ (ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer)` 
by METIS_TAC [abs_rel_def] >>
EXISTS_TAC ``SUC 0: num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, ds_abs1_dr_tr_cases,
COMB_ABS1_XFER_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_xfer_operations (comb_abs1_xfer_operations ds_abs1)`` >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_ready_op_def, DRIVER_ABS1_XFER_ENABLE_def, 
driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_xfer_update *)
DISJ2_TAC >>
`~ (ds_abs1.ds_abs1_xfer.xfer_cur_length < LENGTH ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer)` 
by METIS_TAC [abs_rel_def] >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``driver_abs1_xfer_operations (comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1)) `` >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
EXISTS_TAC ``comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1)`` >>
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases, ds_abs1_comb_tr_cases, ds_abs1_dr_tr_cases,
COMB_ABS1_XFER_ENABLE_def, SPI_ABS1_XFER_ENABLE_def, DRIVER_ABS1_XFER_ENABLE_def,
spi_abs1_xfer_operations_def, spi_abs1_xfer_update_op_def, comb_abs1_xfer_operations_def,
comb_abs1_xfer_ready_op_def, driver_abs1_xfer_operations_def, driver_abs1_xfer_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds when ds_abs0 peforms tau transitions *)
val abs_rel_holds_abs0_tau = store_thm("abs_rel_holds_abs_tau",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ABS0_TAU_LBL_ENABLE ds_abs0) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1') \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 tau ds_abs1' /\ abs_rel (abs0_tau_op ds_abs0) ds_abs1')``,
rw [ABS0_TAU_LBL_ENABLE_def] >>
rw [abs_rel_holds_tau_abs0_rx_update, abs_rel_holds_tau_abs0_rx_reading,
abs_rel_holds_tau_abs0_rx_next, abs_rel_holds_tau_abs0_xfer_done]);


val _ = export_theory();
