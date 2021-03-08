open HolKernel bossLib boolLib Parse;
open listTheory ds_abs0_stateTheory;

val _ = new_theory "ds_abs0_tx";

(* call_tx_ds_abs0: call ds_abs0 to apply tx mode. *)
val call_tx_ds_abs0_def = Define `
call_tx_ds_abs0 (ds_abs0:ds_abs0_state) (buffer:word8 list) =
ds_abs0 with <| ds_abs0_tx := ds_abs0.ds_abs0_tx with
<| tx_data_buffer := buffer; tx_cur_length := 0 |>;
state := abs0_tx |>`

(* abs0_tx_op: TX label related function, perform data transmission. *)
val abs0_tx_op_def = Define `
abs0_tx_op (ds_abs0:ds_abs0_state) =
(ds_abs0 with <|
state := if ds_abs0.ds_abs0_tx.tx_cur_length < ((LENGTH ds_abs0.ds_abs0_tx.tx_data_buffer) - 1) then abs0_tx else abs0_ready;
ds_abs0_tx := ds_abs0.ds_abs0_tx with tx_cur_length := ds_abs0.ds_abs0_tx.tx_cur_length + 1 |>,
SOME (EL (ds_abs0.ds_abs0_tx.tx_cur_length) (ds_abs0.ds_abs0_tx.tx_data_buffer)))`

val abs0_tx_op_state_def = Define `
abs0_tx_op_state (ds_abs0:ds_abs0_state) =
let (ds_abs0', d) = abs0_tx_op ds_abs0 in ds_abs0'`

val abs0_tx_op_value_def = Define `
abs0_tx_op_value (ds_abs0:ds_abs0_state) =
let (ds_abs0', d) = abs0_tx_op ds_abs0 in d`

val _ = export_theory();
