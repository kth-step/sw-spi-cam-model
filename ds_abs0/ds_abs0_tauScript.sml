open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory ds_abs0_rxTheory ds_abs0_xferTheory;

val _ = new_theory "ds_abs0_tau";

(* ABS0_TAU_LBL_ENABLE: ds_abs0_state -> bool *)
val ABS0_TAU_LBL_ENABLE_def = Define `
ABS0_TAU_LBL_ENABLE (ds_abs0:ds_abs0_state) =
((ds_abs0.state = abs0_rx_update) \/
(ds_abs0.state = abs0_rx_reading) \/
(ds_abs0.state = abs0_rx_next) \/
(ds_abs0.state = abs0_xfer_done))`

(* abs0_tau_op: ds_abs0_state -> ds_abs0_state *)
val abs0_tau_op_def = Define `
abs0_tau_op (ds_abs0:ds_abs0_state) =
case ds_abs0.state of
  | abs0_init => ds_abs0 with err := T
  | abs0_ready => ds_abs0 with err := T
  | abs0_tx => ds_abs0 with err := T
  | abs0_rx_idle => ds_abs0 with err := T
  | abs0_rx_update => abs0_rx_update_op ds_abs0
  | abs0_rx_reading => abs0_rx_reading_op ds_abs0
  | abs0_rx_next => abs0_rx_next_op ds_abs0
  | abs0_xfer_idle => ds_abs0 with err := T
  | abs0_xfer_done => abs0_xfer_tau_op ds_abs0`

val _ = export_theory();