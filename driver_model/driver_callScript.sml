open HolKernel bossLib boolLib Parse;
open driver_stateTheory;

val _ = new_theory "driver_call";

(* call_init_dr: call the driver to initialize the controller. *)
val call_init_dr_def = Define `
call_init_dr (dr:driver_state) =
dr with state := dr_init_idle`

(* call_tx_dr: call the driver to transmit a buffer using tx mode. *)
val call_tx_dr_def = Define `
call_tx_dr (dr:driver_state) (buffer:word8 list) =
dr with <| dr_tx := dr.dr_tx with <| tx_data_buf := buffer; tx_cur_length := 0 |>;
state := dr_tx_idle |>`

(* call_rx_dr: call the driver to receive some data using rx mode. *)
val call_rx_dr_def = Define `
call_rx_dr (dr:driver_state) (length: num) =
dr with <| dr_rx := dr.dr_rx with <| rx_left_length := length; rx_data_buf := [] |>;
state := dr_rx_idle |>`

(* call_xfer_dr: call the driver to transmit and receive using xfer mode. *)
val call_xfer_dr_def = Define `
call_xfer_dr (dr:driver_state) (buffer:word8 list) =
dr with <| dr_xfer := dr.dr_xfer with <| xfer_dataOUT_buf := buffer; xfer_dataIN_buf := [];
xfer_cur_length := 0 |>;
state := dr_xfer_idle |>`

(* call_back_dr: the driver returns the received data to other programs. *)
val call_back_dr_def = Define `
call_back_dr (dr:driver_state) =
if dr.state = dr_rx_sendback then
(dr with state := dr_ready,dr.dr_rx.rx_data_buf)
else if dr.state = dr_xfer_sendback then
(dr with state := dr_ready,dr.dr_xfer.xfer_dataIN_buf)
else (dr with dr_err := T, [])`

val call_back_dr_state = Define `
call_back_dr_state (dr:driver_state) =
let (dr',l) = call_back_dr dr in dr'`

val call_back_dr_data = Define `
call_back_dr_data (dr:driver_state) =
let (dr',l) = call_back_dr dr in l`

val _ = export_theory();
