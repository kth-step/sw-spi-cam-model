open HolKernel bossLib boolLib Parse;
open driver_stateTheory;

val _ = new_theory "driver_call";

(* call_init_dr: driver_state -> driver_state *)
val call_init_dr_def = Define `
call_init_dr (dr:driver_state) =
dr with dr_init := dr.dr_init with state := dr_init_idle`

(* call_tx_dr: driver_state -> word8 list -> driver_state *)
val call_tx_dr_def = Define `
call_tx_dr (dr:driver_state) (buffer:word8 list) =
dr with dr_tx := dr.dr_tx with
<| state := dr_tx_idle;
data_buf := buffer;
tx_left_length := LENGTH buffer |>`

(* call_rx_dr: driver_state -> num -> driver_state *)
val call_rx_dr_def = Define `
call_rx_dr (dr:driver_state) (length: num) =
dr with dr_rx := dr.dr_rx with
<| state := dr_rx_idle;
rx_left_length := length;
rx_data_buf := [] |>`

(* call_xfer_dr: driver_state -> word8 list -> driver_state *)
val call_xfer_dr_def = Define `
call_xfer_dr (dr:driver_state) (buffer:word8 list) =
dr with dr_xfer := dr.dr_xfer with
<| state := dr_xfer_idle;
xfer_dataOUT_buf := buffer;
xfer_dataIN_buf := [];
xfer_left_length := LENGTH buffer|>`

val _ = export_theory();
