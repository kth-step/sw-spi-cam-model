open HolKernel bossLib boolLib Parse;
open SPI_stateTheory weak_bisimulationTheory ds_abs0_relTheory abs_relTheory ds_abs0_initTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_xferTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_call_lbl";

(* Theorems for abs0_weak_simulation with call_label *)

(* abs_rel holds for call_init label when ds_abs0 has call_init transition *)
val abs0_abs_rel_call_init = store_thm("abs0_abs_rel_call_init",
``!ds_abs0 ds_abs1 ds_abs0'.
(abs_rel ds_abs0 ds_abs1) /\ (ABS0_CALL_INIT_ENABLE ds_abs0) ==>
(?ds_abs1'. (ds_abs1_tr ds_abs1 call_init ds_abs1') /\ 
(abs_rel (call_init_ds_abs0 ds_abs0) ds_abs1')) \/ 
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 call_init ds_abs1' /\ abs_rel (call_init_ds_abs0 ds_abs0) ds_abs1')``,
rw [ABS0_CALL_INIT_ENABLE_def, call_init_ds_abs0_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >|
[(* ds_abs0.state = abs0_init *)
DISJ1_TAC >>
`ds_abs1.state = abs1_init_pre` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs1_tr_cases, call_init_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* ds_abs0.state = abs0_ready *)
`ds_abs1.state = abs1_ready \/ ds_abs1.state = abs1_init_start \/
 ds_abs1.state = abs1_tx_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* ds_abs1.state = abs1_ready *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, call_init_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* ds_abs1.state = abs1_init_start *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_INIT_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [comb_abs1_init_operations_def, comb_abs1_init_start_op_def, call_init_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* ds_abs1.state = abs1_tx_reset *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, 
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, call_init_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]]);

(* abs_rel holds for call_tx label when ds_abs0 has call_tx transition *)
val abs0_abs_rel_call_tx = store_thm("abs0_abs_rel_call_tx",
``!ds_abs0 ds_abs1 buffer.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_ready) /\ (buffer <> []) ==>
(?ds_abs1'. (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') /\ 
(abs_rel (call_tx_ds_abs0 ds_abs0 buffer) ds_abs1')) \/ 
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1' /\ 
abs_rel (call_tx_ds_abs0 ds_abs0 buffer) ds_abs1')``,
rw [call_tx_ds_abs0_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_ready \/ ds_abs1.state = abs1_init_start \/
 ds_abs1.state = abs1_tx_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* ds_abs1.state = abs1_ready *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, call_tx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* ds_abs1.state = abs1_init_start *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_INIT_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [comb_abs1_init_operations_def, comb_abs1_init_start_op_def, call_tx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* ds_abs1.state = abs1_tx_reset *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, 
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, call_tx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds for call_rx label when ds_abs0 has call_rx transition *)
val abs0_abs_rel_call_rx = store_thm("abs0_abs_rel_call_rx",
``!ds_abs0 ds_abs1 length.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_ready) /\ (length > 0) ==>
(?ds_abs1'. (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1') /\
(abs_rel (call_rx_ds_abs0 ds_abs0 length) ds_abs1')) \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 (call_rx length) ds_abs1' /\
abs_rel (call_rx_ds_abs0 ds_abs0 length) ds_abs1')``,
rw [call_rx_ds_abs0_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_ready \/ ds_abs1.state = abs1_init_start \/
 ds_abs1.state = abs1_tx_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_ready *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, call_rx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_init_start *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_INIT_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [comb_abs1_init_operations_def, comb_abs1_init_start_op_def, call_rx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_tx_reset *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, 
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, call_rx_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds for call_xfer label when ds_abs0 has call_xfer transition *)
val abs0_abs_rel_call_xfer = store_thm("abs0_abs_rel_call_xfer",
``!ds_abs0 ds_abs1 buffer.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_ready) /\ (buffer <> []) ==>
(?ds_abs1'. (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') /\ 
(abs_rel (call_xfer_ds_abs0 ds_abs0 buffer) ds_abs1')) \/
(?n ds_abs1'. n_tau_tr n ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1' /\
abs_rel (call_xfer_ds_abs0 ds_abs0 buffer) ds_abs1')``,
rw [call_xfer_ds_abs0_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_ready \/ ds_abs1.state = abs1_init_start \/
 ds_abs1.state = abs1_tx_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_ready *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, call_xfer_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_init_start *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases,
COMB_ABS1_INIT_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [comb_abs1_init_operations_def, comb_abs1_init_start_op_def, call_xfer_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_tx_reset *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases, 
COMB_ABS1_TX_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, call_xfer_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);

(* abs_rel holds for call_back label when ds_abs0.state = abs0_rx_reply *)
val abs0_abs_rel_call_back_rx_reply = store_thm("abs0_abs_rel_call_back_rx_reply",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_rx_reply) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_back (call_back_ds_abs0_data ds_abs0)) ds_abs1') /\ 
(abs_rel (call_back_ds_abs0_state ds_abs0) ds_abs1')``,
rw [call_back_ds_abs0_data_def,call_back_ds_abs0_state_def,call_back_ds_abs0_def,
call_back_ds_abs0_rx_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_rx_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs1_tr_cases,call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,
call_back_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_back label when ds_abs0.state = abs0_xfer_reply *)
val abs0_abs_rel_call_back_xfer_reply = store_thm("abs0_abs_rel_call_back_xfer_reply",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_xfer_reply) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_back (call_back_ds_abs0_data ds_abs0)) ds_abs1') /\ 
(abs_rel (call_back_ds_abs0_state ds_abs0) ds_abs1')``,
rw [call_back_ds_abs0_data_def,call_back_ds_abs0_state_def,call_back_ds_abs0_def,
call_back_ds_abs0_xfer_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_xfer_reset` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs1_tr_cases,call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,
call_back_ds_abs1_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);
        
(* Theorems for abs1_weak_simulation with call labels *)
(* abs_rel holds for call_init label when ds_abs1 state is abs1_init_pre *)
val abs1_init_pre_abs_rel_call_init = store_thm("abs1_init_pre_abs_rel_call_init",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_init_pre) ==>
?ds_abs0'. (ds_abs0_tr ds_abs0 call_init ds_abs0') /\ 
(abs_rel ds_abs0' (call_init_ds_abs1 ds_abs1))``,
rw [call_init_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_init` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, ABS0_CALL_INIT_ENABLE_def, call_init_ds_abs0_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_init label when ds_abs1 state is abs1_ready *)
val abs1_ready_abs_rel_call_init = store_thm("abs1_ready_abs_rel_call_init",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_ready) ==>
?ds_abs0'. (ds_abs0_tr ds_abs0 call_init ds_abs0') /\ 
(abs_rel ds_abs0' (call_init_ds_abs1 ds_abs1))``,
rw [call_init_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_ready` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, ABS0_CALL_INIT_ENABLE_def, call_init_ds_abs0_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_tx label when ds_abs1 has call_tx transition *)
val abs1_abs_rel_call_tx = store_thm("abs1_abs_rel_call_tx",
``!ds_abs0 ds_abs1 buffer.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_ready) /\ (buffer <> []) ==>
?ds_abs0'. (ds_abs0_tr ds_abs0 (call_tx buffer) ds_abs0') /\
(abs_rel ds_abs0' (call_tx_ds_abs1 ds_abs1 buffer))``,
rw [call_tx_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_ready` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, call_tx_ds_abs0_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_rx label when ds_abs1 has call_rx transition *)
val abs1_abs_rel_call_rx = store_thm("abs1_abs_rel_call_rx",
``!ds_abs0 ds_abs1 length.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_ready) /\ (length > 0) ==>
?ds_abs0'. (ds_abs0_tr ds_abs0 (call_rx length) ds_abs0') /\
(abs_rel ds_abs0' (call_rx_ds_abs1 ds_abs1 length))``,
rw [call_rx_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_ready` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, call_rx_ds_abs0_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_xfer label when ds_abs1 has call_xfer transition *)
val abs1_abs_rel_call_xfer = store_thm("abs1_abs_rel_call_xfer",
``!ds_abs0 ds_abs1 buffer.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_ready) /\ (buffer <> []) ==>
?ds_abs0'. (ds_abs0_tr ds_abs0 (call_xfer buffer) ds_abs0') /\
(abs_rel ds_abs0' (call_xfer_ds_abs1 ds_abs1 buffer))``,
rw [call_xfer_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_ready` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, call_xfer_ds_abs0_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_back label when ds_abs1.state = abs1_rx_reset *)
val abs1_abs_rel_call_back_rx_reset = store_thm("abs1_abs_rel_call_back_rx_reset",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_rx_reset) ==>
?ds_abs0'.
(ds_abs0_tr ds_abs0 (call_back (call_back_ds_abs1_data ds_abs1)) ds_abs0') /\
(abs_rel ds_abs0' (call_back_ds_abs1_state ds_abs1))``,
rw [call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,call_back_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_rx_reply` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, call_back_ds_abs0_state_def,call_back_ds_abs0_data_def,
call_back_ds_abs0_def,call_back_ds_abs0_rx_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for call_back label when ds_abs1.state = abs1_xfer_reset *)
val abs1_abs_rel_call_back_xfer_reset = store_thm("abs1_abs_rel_call_back_xfer_reset",
``!ds_abs0 ds_abs1.
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_xfer_reset) ==>
?ds_abs0'.
(ds_abs0_tr ds_abs0 (call_back (call_back_ds_abs1_data ds_abs1)) ds_abs0') /\
(abs_rel ds_abs0' (call_back_ds_abs1_state ds_abs1))``,
rw [call_back_ds_abs1_data_def,call_back_ds_abs1_state_def,call_back_ds_abs1_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_xfer_reply` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, call_back_ds_abs0_state_def,call_back_ds_abs0_data_def,
call_back_ds_abs0_def,call_back_ds_abs0_xfer_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);                                           

val _ = export_theory();
