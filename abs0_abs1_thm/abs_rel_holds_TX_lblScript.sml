open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory weak_bisimulationTheory ds_abs0_relTheory abs_relTheory ds_abs0_txTheory ds_abs1_relTheory ds_abs1_txTheory;

val _ = new_theory "abs_rel_holds_TX_lbl";

(* abs_rel holds when ds_abs1 peforms TX label transition *)
val abs_rel_holds_abs1_TX_lbl = store_thm("abs_rel_holds_abs1_TX_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ABS1_TX_LBL_ENABLE ds_abs1) ==>
?ds_abs0'. ds_abs0_tr ds_abs0 (TX (abs1_tx_trans_done_op_value ds_abs1)) ds_abs0' /\ 
abs_rel ds_abs0' (abs1_tx_trans_done_op_state ds_abs1)``,
rw [ABS1_TX_LBL_ENABLE_def, abs1_tx_trans_done_op_state_def, 
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_tx` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_tx_done_1 *)
`ds_abs1.ds_abs1_tx.tx_cur_length = ds_abs0.ds_abs0_tx.tx_cur_length + 1` by METIS_TAC [abs_rel_def] >>
`~ (ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer)` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = ds_abs0.ds_abs0_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`~ (ds_abs0.ds_abs0_tx.tx_cur_length < LENGTH ds_abs0.ds_abs0_tx.tx_data_buffer - 1)` by fs [] >>
rw [ds_abs0_tr_cases, abs0_tx_op_value_def, abs0_tx_op_state_def, abs0_tx_op_def] >|
[fs [abs_rel_def],
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* abs1_tx_done_2 *)
`ds_abs1.ds_abs1_tx.tx_cur_length = ds_abs0.ds_abs0_tx.tx_cur_length + 1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = ds_abs0.ds_abs0_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs0.ds_abs0_tx.tx_cur_length < LENGTH ds_abs0.ds_abs0_tx.tx_data_buffer - 1` by fs [] >>
rw [ds_abs0_tr_cases, abs0_tx_op_value_def, abs0_tx_op_state_def, abs0_tx_op_def] >|
[fs [abs_rel_def],
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* abs1_tx_next *)
`ds_abs1.ds_abs1_tx.tx_cur_length = ds_abs0.ds_abs0_tx.tx_cur_length + 2` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = ds_abs0.ds_abs0_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs0.ds_abs0_tx.tx_cur_length < LENGTH ds_abs0.ds_abs0_tx.tx_data_buffer - 1` by fs [] >>
rw [ds_abs0_tr_cases, abs0_tx_op_value_def, abs0_tx_op_state_def, abs0_tx_op_def] >|
[fs [abs_rel_def],
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* abs1_tx_last *)
`ds_abs1.ds_abs1_tx.tx_cur_length = ds_abs0.ds_abs0_tx.tx_cur_length + 2` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length = LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = ds_abs0.ds_abs0_tx.tx_data_buffer` by METIS_TAC [abs_rel_def] >>
`ds_abs0.ds_abs0_tx.tx_cur_length < LENGTH ds_abs0.ds_abs0_tx.tx_data_buffer - 1` by fs [] >>
rw [ds_abs0_tr_cases, abs0_tx_op_value_def, abs0_tx_op_state_def, abs0_tx_op_def] >|
[fs [abs_rel_def],
fs [abs_rel_def, IS_ABS_STATE_REL_def]]]);

(* abs_rel holds when ds_abs0 peforms TX label transition *)
val abs_rel_holds_abs0_TX_lbl = store_thm("abs_rel_holds_abs0_TX_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_tx) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 (TX (abs0_tx_op_value ds_abs0)) ds_abs1' /\ 
abs_rel (abs0_tx_op_state ds_abs0) ds_abs1') \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 (TX (abs0_tx_op_value ds_abs0)) ds_abs1' /\
abs_rel (abs0_tx_op_state ds_abs0) ds_abs1')``,
rw [abs0_tx_op_value_def, abs0_tx_op_state_def, abs0_tx_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >|
[(* not the last one *)
`ds_abs1.state = abs1_tx_done_1 \/ ds_abs1.state = abs1_tx_data_1 \/ 
ds_abs1.state = abs1_tx_last_update \/ ds_abs1.state = abs1_tx_done_2 \/
ds_abs1.state = abs1_tx_next \/ ds_abs1.state = abs1_tx_last \/
ds_abs1.state = abs1_tx_data_2 \/ ds_abs1.state = abs1_tx_update \/
ds_abs1.state = abs1_tx_trans \/ ds_abs1.state = abs1_tx_idle` by fs [IS_ABS_STATE_REL_def] >|
[(* not the last one, abs1_tx_done_1 *)
fs [abs_rel_def],
(* not the last one, abs1_tx_data_1 *)
fs [abs_rel_def],
(* not the last one, abs1_tx_last_update *)
fs [abs_rel_def],
(* not the last one, abs1_tx_done_2 *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_TX_LBL_ENABLE_def, abs1_tx_trans_done_op_state_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_tx_next *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_TX_LBL_ENABLE_def, abs1_tx_trans_done_op_state_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_tx_last *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_TX_LBL_ENABLE_def, abs1_tx_trans_done_op_state_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >|
[`ds_abs1.spi_abs1.TX_SHIFT_REG = 
EL (ds_abs1.ds_abs1_tx.tx_cur_length - 2) ds_abs1.ds_abs1_tx.tx_data_buffer` by fs [abs_rel_def] >>
`ds_abs0.ds_abs0_tx.tx_cur_length  = ds_abs1.ds_abs1_tx.tx_cur_length - 2` by fs [abs_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = ds_abs0.ds_abs0_tx.tx_data_buffer` by fs [abs_rel_def] >>
fs [],
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* not the last one, abs1_tx_data_2 *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_2_op_def, abs1_tx_trans_done_op_value_def,
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one abs1_tx_update *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_update_op_def, abs1_tx_trans_done_op_value_def,
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_tx_trans *)
`ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer - 1` by fs [abs_rel_def] >>
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
EXISTS_TAC ``spi_abs1_tx_operations (comb_abs1_tx_operations ds_abs1)`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, spi_abs1_tx_operations_def, spi_abs1_tx_data_2_op_def, 
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_state_def, 
abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* not the last one, abs1_tx_idle *)
`ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer - 1` by fs [abs_rel_def] >>
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC ,ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def,
GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
EXISTS_TAC ``comb_abs1_tx_operations (spi_abs1_tx_operations ds_abs1)`` >>
EXISTS_TAC ``spi_abs1_tx_operations 
(comb_abs1_tx_operations (spi_abs1_tx_operations ds_abs1))`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def, ds_abs1_comb_tr_cases, 
ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def, COMB_ABS1_TX_ENABLE_def, spi_abs1_tx_operations_def, 
spi_abs1_tx_data_2_op_def, spi_abs1_tx_idle_op_def, abs1_tx_trans_done_op_value_def, 
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]],
(* last one *)
`ds_abs1.state = abs1_tx_done_2 \/ ds_abs1.state = abs1_tx_next \/
ds_abs1.state = abs1_tx_last \/ ds_abs1.state = abs1_tx_data_2 \/
ds_abs1.state = abs1_tx_update \/ ds_abs1.state = abs1_tx_done_1 \/
ds_abs1.state = abs1_tx_data_1 \/ ds_abs1.state = abs1_tx_last_update \/
ds_abs1.state = abs1_tx_trans \/ ds_abs1.state = abs1_tx_idle` by fs [IS_ABS_STATE_REL_def] >|
[(* last one, abs1_tx_done_2 *)
fs [abs_rel_def],
(* last one, abs1_tx_next *)
fs [abs_rel_def],
(* last one, abs1_tx_last *)
fs [abs_rel_def],
(* last one, abs1_tx_data_2 *)
fs [abs_rel_def],
(* last one, abs1_tx_update *)
fs [abs_rel_def],
(* last one, abs1_tx_done_1 *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, ABS1_TX_LBL_ENABLE_def, abs1_tx_trans_done_op_state_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_tx_data_1 *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_1_op_def, abs1_tx_trans_done_op_value_def,
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_tx_last_update *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_last_update_op_def, abs1_tx_trans_done_op_value_def,
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_tx_trans *)
`~ (ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer - 1)` by fs [abs_rel_def] >>
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
EXISTS_TAC ``spi_abs1_tx_operations (comb_abs1_tx_operations ds_abs1)`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def, ds_abs1_spi_tr_cases, 
SPI_ABS1_TX_ENABLE_def, spi_abs1_tx_operations_def, spi_abs1_tx_data_1_op_def, 
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_state_def, 
abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* last one, abs1_tx_idle *)
`~ (ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer - 1)` by fs [abs_rel_def] >>
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC ,ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def,
GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
EXISTS_TAC ``comb_abs1_tx_operations (spi_abs1_tx_operations ds_abs1)`` >>
EXISTS_TAC ``spi_abs1_tx_operations 
(comb_abs1_tx_operations (spi_abs1_tx_operations ds_abs1))`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def, ds_abs1_comb_tr_cases, 
ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def, COMB_ABS1_TX_ENABLE_def, spi_abs1_tx_operations_def, 
spi_abs1_tx_data_1_op_def, spi_abs1_tx_idle_op_def, abs1_tx_trans_done_op_value_def, 
abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def, ABS1_TX_LBL_ENABLE_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]]);

val _ = export_theory();
