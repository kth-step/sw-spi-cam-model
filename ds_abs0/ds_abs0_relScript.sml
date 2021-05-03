open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs0_stateTheory ds_abs0_initTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_xferTheory ds_abs0_tauTheory;

val _ = new_theory "ds_abs0_rel";

(* return the received data buffer*)
val call_back_ds_abs0_def = Define `
call_back_ds_abs0 (ds_abs0:ds_abs0_state) =
if ds_abs0.state = abs0_rx_reply then call_back_ds_abs0_rx ds_abs0
else if ds_abs0.state = abs0_xfer_reply then call_back_ds_abs0_xfer ds_abs0
else (ds_abs0 with err := T, [])`

val call_back_ds_abs0_state = Define `
call_back_ds_abs0_state (ds_abs0:ds_abs0_state) =
let (ds_abs0',l) = call_back_ds_abs0 ds_abs0 in ds_abs0'`

val call_back_ds_abs0_data = Define `
call_back_ds_abs0_data (ds_abs0:ds_abs0_state) =
let (ds_abs0',l) = call_back_ds_abs0 ds_abs0 in l`

(* ds_abs0_tr: the state transition relation for ds_abs0 model. *)
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
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_rx_reply) \/ (ds_abs0.state = abs0_xfer_reply) ==>
ds_abs0_tr ds_abs0 (call_back (call_back_ds_abs0_data ds_abs0)) 
(call_back_ds_abs0_state ds_abs0)) /\
(* TX/RX/XFER *)
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_tx) ==>
ds_abs0_tr ds_abs0 (TX (abs0_tx_op_value ds_abs0)) (abs0_tx_op_state ds_abs0)) /\
(!(ds_abs0:ds_abs0_state). (ABS0_RX_LBL_ENABLE ds_abs0) /\ (data <> NONE) ==>
ds_abs0_tr ds_abs0 (RX data) (abs0_rx_op ds_abs0 data)) /\
(!(ds_abs0:ds_abs0_state). (ds_abs0.state = abs0_xfer_idle) /\ (dataIN <> NONE) ==>
ds_abs0_tr ds_abs0 (XFER dataIN (abs0_xfer_op_value ds_abs0 dataIN))
(abs0_xfer_op_state ds_abs0 dataIN)) /\
(* tau transitions *)
(!(ds_abs0:ds_abs0_state). (ABS0_TAU_LBL_ENABLE ds_abs0) ==>
ds_abs0_tr ds_abs0 tau (abs0_tau_op ds_abs0))`

(* abs0_global_tr: the global state transition relation for 2 ds_abs0 devices. *)
val (abs0_global_tr_rules, abs0_global_tr_ind, abs0_global_tr_cases) = Hol_reln `
(!d0 d1 d0'. ds_abs0_tr d0 call_init d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 d1'. ds_abs0_tr d1 call_init d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 d0' buffer. ds_abs0_tr d0 (call_tx buffer) d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 d1' buffer. ds_abs0_tr d1 (call_tx buffer) d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 d0' l. ds_abs0_tr d0 (call_rx l) d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 d1' l. ds_abs0_tr d1 (call_rx l) d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 buffer0 d0'. 
ds_abs0_tr d0 (call_xfer buffer0) d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 buffer1 d1'. 
ds_abs0_tr d1 (call_xfer buffer1) d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 buffer0 d0'. 
ds_abs0_tr d0 (call_back buffer0) d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 buffer1 d1'. 
ds_abs0_tr d1 (call_back buffer1) d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 d0'. ds_abs0_tr d0 tau d0' ==>
abs0_global_tr (d0, d1) tau (d0', d1)) /\
(!d0 d1 d1'. ds_abs0_tr d1 tau d1' ==>
abs0_global_tr (d0, d1) tau (d0, d1')) /\
(!d0 d1 data d0' d1'. ds_abs0_tr d0 (TX data) d0' /\ ds_abs0_tr d1 (RX data) d1' ==>
abs0_global_tr (d0, d1) tau (d0', d1')) /\
(!d0 d1 data d0' d1'. ds_abs0_tr d0 (RX data) d0' /\ ds_abs0_tr d1 (TX data) d1' ==>
abs0_global_tr (d0, d1) tau (d0', d1')) /\
(!d0 d1 dataI dataO d0' d1'. 
ds_abs0_tr d0 (XFER dataI dataO) d0' /\ ds_abs0_tr d1 (XFER dataO dataI) d1' ==>
abs0_global_tr (d0, d1) tau (d0', d1'))`

val _ = export_theory();
