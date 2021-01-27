open HolKernel bossLib boolLib Parse;
open listTheory;
open ds_abs0_stateTheory;

val _ = new_theory "ds_abs0_rx";

(* call_rx_ds_abs0: ds_abs0_state -> num -> ds_abs0_state *)
val call_rx_ds_abs0_def = Define `
call_rx_ds_abs0 (ds_abs0:ds_abs0_state) (length:num) =
ds_abs0 with <| ds_abs0_rx := ds_abs0.ds_abs0_rx with
<| rx_left_length := length; rx_data_buffer := [] |>;
state := abs0_rx_idle |>`

(* RX label functions *)
val ABS0_RX_LBL_ENABLE_def = Define `
ABS0_RX_LBL_ENABLE (ds_abs0:ds_abs0_state) =
((ds_abs0.state = abs0_rx_idle) \/
(ds_abs0.state = abs0_rx_reading))`

(* abs0_rx_idle_op: ds_abs0_state -> word8 option -> ds_abs0_state *)
val abs0_rx_idle_op_def = Define `
abs0_rx_idle_op (ds_abs0:ds_abs0_state) (data:word8 option) =
ds_abs0 with
<| state := abs0_rx_update;
ds_abs0_rx := ds_abs0.ds_abs0_rx with temp_RSR := THE data |>`

(* abs0_rx_reading_op: ds_abs0_state -> word8 option -> ds_abs0_state *)
val abs0_rx_reading_op_def = Define `
abs0_rx_reading_op (ds_abs0:ds_abs0_state) (data:word8 option) =
ds_abs0 with 
<| state := abs0_rx_next;
ds_abs0_rx := ds_abs0.ds_abs0_rx with 
<| temp_RSR := THE data; temp_value := ds_abs0.ds_abs0_rx.temp_RSR |> |>`

(* abs0_rx_op: ds_abs0_state -> word8 option -> ds_abs0_state *)
val abs0_rx_op_def = Define `
abs0_rx_op (ds_abs0:ds_abs0_state) (data:word8 option) =
if ds_abs0.state = abs0_rx_idle then
(abs0_rx_idle_op ds_abs0 data)
else if ds_abs0.state = abs0_rx_reading then
(abs0_rx_reading_op ds_abs0 data)
else ds_abs0 with err := T`

(* tau functions for rx automaton *)
(* abs0_rx_update_op: ds_abs0_state -> ds_abs0_state *)
val abs0_rx_update_tau_op_def = Define `
abs0_rx_update_tau_op (ds_abs0:ds_abs0_state) =
ds_abs0 with
state := if ds_abs0.ds_abs0_rx.rx_left_length > 0 then abs0_rx_reading else abs0_ready`

(* abs0_rx_reading_op: ds_abs0_state -> ds_abs0_state *)
val abs0_rx_reading_tau_op_def = Define `
abs0_rx_reading_tau_op (ds_abs0:ds_abs0_state) =
ds_abs0 with 
<| state := abs0_rx_idle;
ds_abs0_rx := ds_abs0.ds_abs0_rx with
<| rx_data_buffer := ds_abs0.ds_abs0_rx.rx_data_buffer ++ [ds_abs0.ds_abs0_rx.temp_RSR];
   rx_left_length := ds_abs0.ds_abs0_rx.rx_left_length - 1 |> |>`

(* abs0_rx_next_op: ds_abs0_state -> ds_abs0_state *)
val abs0_rx_next_tau_op_def = Define `
abs0_rx_next_tau_op (ds_abs0:ds_abs0_state) =
ds_abs0 with 
<| state := abs0_rx_update;
ds_abs0_rx := ds_abs0.ds_abs0_rx with
<| rx_data_buffer := ds_abs0.ds_abs0_rx.rx_data_buffer ++ [ds_abs0.ds_abs0_rx.temp_value];
   rx_left_length := ds_abs0.ds_abs0_rx.rx_left_length - 1 |> |>`

val _ = export_theory();
