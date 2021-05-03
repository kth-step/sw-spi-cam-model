open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory ds_abs0_relTheory abs_relTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_abs1_tau_comb";

(* abs_rel holds for ds_abs1 tau_comb in the init automaton *)
val abs_rel_holds_abs1_tau_comb_init = store_thm("abs_rel_holds_abs1_tau_comb_init",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (COMB_ABS1_INIT_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (comb_abs1_init_operations ds_abs1))``,
rw [COMB_ABS1_INIT_ENABLE_def, comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for ds_abs1 tau_comb in the tx automaton *)
val abs_rel_holds_abs1_tau_comb_tx = store_thm("abs_rel_holds_abs1_tau_comb_tx",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (COMB_ABS1_TX_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (comb_abs1_tx_operations ds_abs1))``,
rw [COMB_ABS1_TX_ENABLE_def, comb_abs1_tx_operations_def] >>
rw [comb_abs1_tx_trans_op_def, comb_abs1_tx_done_2_op_def, comb_abs1_tx_reset_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def] >> 
`ds_abs1.ds_abs1_tx.tx_cur_length = ds_abs0.ds_abs0_tx.tx_cur_length + 1` by fs [] >|
[fs[],
`ds_abs1.ds_abs1_tx.tx_cur_length < LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer` by fs [] >>
fs[]]);

(* abs_rel holds for ds_abs1 tau_comb in the rx automaton *)
val abs_rel_holds_abs1_tau_comb_rx = store_thm("abs_rel_holds_abs1_tau_comb_rx",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (COMB_ABS1_RX_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (comb_abs1_rx_operations ds_abs1))``,
rw [COMB_ABS1_RX_ENABLE_def, comb_abs1_rx_operations_def,
comb_abs1_rx_read_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for ds_abs1 tau_comb in the xfer automaton *)
val abs_rel_holds_abs1_tau_comb_xfer = store_thm("abs_rel_holds_abs1_tau_comb_xfer",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (COMB_ABS1_XFER_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (comb_abs1_xfer_operations ds_abs1))``,
rw [COMB_ABS1_XFER_ENABLE_def, comb_abs1_xfer_operations_def] >>
rw [comb_abs1_xfer_prepare_op_def, comb_abs1_xfer_ready_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds when ds_abs1 peforms tau_comb *)
val abs_rel_holds_abs1_tau_comb = store_thm("abs_rel_holds_abs1_tau_comb",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (ds_abs1':ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1') ==>
(abs_rel ds_abs0 ds_abs1') \/
(?ds_abs0'. ds_abs0_tr ds_abs0 tau ds_abs0' /\ abs_rel ds_abs0' ds_abs1')``,
rw [ds_abs1_comb_tr_cases] >>
rw [abs_rel_holds_abs1_tau_comb_init, abs_rel_holds_abs1_tau_comb_tx,
abs_rel_holds_abs1_tau_comb_rx, abs_rel_holds_abs1_tau_comb_xfer]);

val _ = export_theory();
