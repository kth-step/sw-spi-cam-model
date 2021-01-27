open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory;
open ds_abs0_relTheory abs_relTheory ds_abs0_txTheory;
open ds_abs1_relTheory ds_abs1_txTheory;

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
cheat);

val _ = export_theory();
