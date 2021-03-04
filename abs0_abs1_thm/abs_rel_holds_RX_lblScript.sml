open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory weak_bisimulationTheory ds_abs0_relTheory abs_relTheory ds_abs0_rxTheory ds_abs1_relTheory ds_abs1_rxTheory;

val _ = new_theory "abs_rel_holds_RX_lbl";

(* abs_rel holds when ds_abs1 peforms RX label transition *)
val abs_rel_holds_abs1_RX_lbl = store_thm("abs_rel_holds_abs1_RX_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (data: word8 option).
(abs_rel ds_abs0 ds_abs1) /\ (ABS1_RX_LBL_ENABLE ds_abs1) /\ (data <> NONE) ==>
?ds_abs0'. ds_abs0_tr ds_abs0 (RX data) ds_abs0' /\ 
abs_rel ds_abs0' (abs1_rx_receive_data_op ds_abs1 data)``,
rw [ABS1_RX_LBL_ENABLE_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >|
[(* abs1_rx_receive *)
`ds_abs0.state = abs0_rx_idle` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, ABS0_RX_LBL_ENABLE_def, abs0_rx_op_def, 
abs1_rx_receive_data_op_def, abs0_rx_idle_op_def, abs1_rx_receive_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_rx_fetch_data *)
`ds_abs0.state = abs0_rx_reading` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, ABS0_RX_LBL_ENABLE_def, abs0_rx_op_def, 
abs1_rx_receive_data_op_def, abs0_rx_reading_op_def, abs1_rx_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds when ds_abs0 peforms RX label transition *)
val abs_rel_holds_abs0_RX_lbl = store_thm("abs_rel_holds_abs0_RX_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (data: word8 option).
(abs_rel ds_abs0 ds_abs1) /\ (ABS0_RX_LBL_ENABLE ds_abs0) /\ (data <> NONE) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 (RX data) ds_abs1' /\
abs_rel (abs0_rx_op ds_abs0 data) ds_abs1')\/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 (RX data) ds_abs1' /\
abs_rel (abs0_rx_op ds_abs0 data) ds_abs1')``,
rw [ABS0_RX_LBL_ENABLE_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >|
[(* abs0_rx_idle *)
rw [abs0_rx_op_def, abs0_rx_idle_op_def] >>
`ds_abs1.state = abs1_rx_receive \/ ds_abs1.state = abs1_rx_idle` 
by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_rx_receive *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_RX_LBL_ENABLE_def, abs1_rx_receive_data_op_def, abs1_rx_receive_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_rx_idle *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_RX_ENABLE_def, 
GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_idle_op_def, ABS1_RX_LBL_ENABLE_def, 
abs1_rx_receive_data_op_def, abs1_rx_receive_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* abs1_rx_reading *)
rw [abs0_rx_op_def, abs0_rx_reading_op_def] >>
`ds_abs1.state = abs1_rx_fetch_data \/ ds_abs1.state = abs1_rx_read` 
by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_rx_fetch_data *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_RX_LBL_ENABLE_def, abs1_rx_receive_data_op_def, abs1_rx_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_rx_read *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, COMB_ABS1_RX_ENABLE_def,
GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_rx_operations ds_abs1`` >>
rw [comb_abs1_rx_operations_def, comb_abs1_rx_read_op_def, ABS1_RX_LBL_ENABLE_def,
abs1_rx_receive_data_op_def, abs1_rx_fetch_data_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]]);

val _ = export_theory();
