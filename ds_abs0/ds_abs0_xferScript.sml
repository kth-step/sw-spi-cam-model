open HolKernel bossLib boolLib Parse;
open listTheory ds_abs0_stateTheory;

val _ = new_theory "ds_abs0_xfer";

(* call_xfer_ds_abs0: ds_abs0_state -> word8 list -> ds_abs0_state *)
val call_xfer_ds_abs0_def = Define `
call_xfer_ds_abs0 (ds_abs0:ds_abs0_state) (buffer:word8 list) =
ds_abs0 with <| ds_abs0_xfer := ds_abs0.ds_abs0_xfer with
<|xfer_dataOUT_buffer := buffer; xfer_dataIN_buffer := []; xfer_cur_length := 0|>;
state := abs0_xfer_idle |>`

(* XFER label functions *)
(* abs0_xfer_op: ds_abs0_state -> word8 option -> ds_abs0_state * word8 option *)
val abs0_xfer_op_def = Define `
abs0_xfer_op (ds_abs0:ds_abs0_state) (data:word8 option) =
if (data <> NONE) then
(ds_abs0 with <| state := abs0_xfer_done;
ds_abs0_xfer := ds_abs0.ds_abs0_xfer with
<| xfer_RSR := THE data;
xfer_cur_length := ds_abs0.ds_abs0_xfer.xfer_cur_length + 1 |> |>,
SOME (EL (ds_abs0.ds_abs0_xfer.xfer_cur_length) (ds_abs0.ds_abs0_xfer.xfer_dataOUT_buffer)))
else (ds_abs0 with err := T, NONE)`

(* functions for abs0_xfer_op that return specific datatypes *)
val abs0_xfer_op_state_def = Define `
abs0_xfer_op_state (ds_abs0:ds_abs0_state) (data:word8 option) =
let (ds_abs0', dataOUT) = abs0_xfer_op ds_abs0 data in ds_abs0'`

val abs0_xfer_op_value_def = Define `
abs0_xfer_op_value (ds_abs0:ds_abs0_state) (data:word8 option) =
let (ds_abs0', dataOUT) = abs0_xfer_op ds_abs0 data in dataOUT`

(* abs0_xfer_tau_op: ds_abs0_state -> ds_abs0_state *)
val abs0_xfer_tau_op_def = Define `
abs0_xfer_tau_op (ds_abs0: ds_abs0_state) =
ds_abs0 with
<| state := if ds_abs0.ds_abs0_xfer.xfer_cur_length < 
(LENGTH ds_abs0.ds_abs0_xfer.xfer_dataOUT_buffer)
then abs0_xfer_idle else abs0_ready;
ds_abs0_xfer := ds_abs0.ds_abs0_xfer with
xfer_dataIN_buffer := ds_abs0.ds_abs0_xfer.xfer_dataIN_buffer ++ [ds_abs0.ds_abs0_xfer.xfer_RSR] |>`

val _ = export_theory();
