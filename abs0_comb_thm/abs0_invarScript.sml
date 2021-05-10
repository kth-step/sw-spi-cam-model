open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory ds_abs0_initTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_xferTheory ds_abs0_tauTheory ds_abs0_relTheory;

val _ = new_theory "abs0_invar";

(* abs0_invar: an invariant of abs0 for state transisitions *)
val abs0_invar_def = Define `
abs0_invar (ds_abs0:ds_abs0_state) = ~ds_abs0.err`

(* the invariant holds during state transitions *)
val abs0_invar_holds = store_thm("abs0_invar_holds",
``!ds_abs0 lbl ds_abs0'.
abs0_invar ds_abs0 ==> 
ds_abs0_tr ds_abs0 lbl ds_abs0' ==>
abs0_invar ds_abs0'``,
rw [ds_abs0_tr_cases,abs0_invar_def] >>
fs [ABS0_CALL_INIT_ENABLE_def,call_init_ds_abs0_def,call_tx_ds_abs0_def,call_rx_ds_abs0_def,
    call_xfer_ds_abs0_def,call_back_ds_abs0_state_def,call_back_ds_abs0_def,
    call_back_ds_abs0_rx_def,call_back_ds_abs0_xfer_def,abs0_tx_op_state_def,abs0_tx_op_def,
    ABS0_RX_LBL_ENABLE_def,abs0_rx_op_def,abs0_rx_idle_op_def,abs0_rx_reading_op_def,
    abs0_xfer_op_state_def,abs0_xfer_op_def,ABS0_TAU_LBL_ENABLE_def,abs0_tau_op_def,
    abs0_rx_update_tau_op_def,abs0_rx_reading_tau_op_def,abs0_rx_next_tau_op_def,
    abs0_xfer_tau_op_def]);

val _ = export_theory();
