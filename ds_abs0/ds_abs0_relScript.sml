open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open ds_abs0_stateTheory ds_abs0_initTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_xferTheory;

val _ = new_theory "ds_abs0_rel";

(* the state transition relation for ds_abs0 model *)
val (ds_abs0_tr_rules, ds_abs0_tr_ind, ds_abs0_tr_cases) = Hol_reln `
(* call_func labels *)
(!(ds_abs0:ds_abs0_state). (ABS0_CALL_INIT_ENABLE ds_abs0) ==> 
ds_abs0_tr ds_abs0 call_init (call_init_ds_abs0 ds_abs0)) /\
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_ready) /\ (buffer <> []) ==>
ds_abs0_tr ds_abs0 (call_tx buffer) (call_tx_ds_abs0 ds_abs0 buffer)) /\
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_ready) /\ (length > 0) ==>
ds_abs0_tr ds_abs0 (call_rx length) (call_rx_ds_abs0 ds_abs0 length)) /\
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_ready) /\ (buffer <> []) ==>
ds_abs0_tr ds_abs0 (call_xfer buffer) (call_xfer_ds_abs0 ds_abs0 buffer)) /\
(* TX/RX/XFER *)
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_tx) ==>
ds_abs0_tr ds_abs0 (TX (abs0_tx_op_value ds_abs0)) (abs0_tx_op_state ds_abs0)) /\
(!(ds_abs0:ds_abs0_state). (ABS0_RX_LBL_ENABLE ds_abs0) /\ (data <> NONE) ==>
ds_abs0_tr ds_abs0 (RX data) (abs0_rx_op ds_abs0 data)) /\
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_idle) /\ (dataIN <> NONE) ==>
ds_abs0_tr ds_abs0 (XFER dataIN (abs0_xfer_op_value ds_abs0 dataIN))
(abs0_xfer_op_state ds_abs0 dataIN)) /\
(* tau transitions *)
(!(ds_abs0:ds_abs0_state). (ABS0_TAU_LBL_ENABLE ds_abs0) ==>
ds_abs0_tr ds_abs0 tau (abs0_tau_op ds_abs0))`

val _ = export_theory();
