open HolKernel bossLib boolLib Parse;
open listTheory ds_abs1_stateTheory;

val _ = new_theory "ds_abs1_tx";

(* SPI_ABS1_TX_ENABLE: ds_abs1's state is permitted to perform SPI controller related internal tx operations. *)
val SPI_ABS1_TX_ENABLE_def = Define `
SPI_ABS1_TX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_tx_idle) \/ 
(ds_abs1.state = abs1_tx_data_1) \/
(ds_abs1.state = abs1_tx_data_2) \/
(ds_abs1.state = abs1_tx_update) \/
(ds_abs1.state = abs1_tx_last_update))`

(* COMB_ABS1_TX_ENABLE: ds_abs1's state is permitted to perform other internal tx operations. *)
val COMB_ABS1_TX_ENABLE_def = Define `
COMB_ABS1_TX_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_tx_trans) \/
(ds_abs1.state = abs1_tx_done_2) \/
(ds_abs1.state = abs1_tx_reset))`

(* SPI controller related internal tx functions. *)
val spi_abs1_tx_idle_op_def = Define `
spi_abs1_tx_idle_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_tx_trans`

val spi_abs1_tx_data_1_op_def = Define `
spi_abs1_tx_data_1_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_tx_done_1;
spi_abs1 := ds_abs1.spi_abs1 with
TX_SHIFT_REG := (EL (ds_abs1.ds_abs1_tx.tx_cur_length - 1) 
(ds_abs1.ds_abs1_tx.tx_data_buffer)) |>`

val spi_abs1_tx_data_2_op_def = Define `
spi_abs1_tx_data_2_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_tx_done_2;
spi_abs1 := ds_abs1.spi_abs1 with
TX_SHIFT_REG := (EL (ds_abs1.ds_abs1_tx.tx_cur_length - 1) 
(ds_abs1.ds_abs1_tx.tx_data_buffer)) |>`

val spi_abs1_tx_update_op_def = Define `
spi_abs1_tx_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_tx_done_2;
spi_abs1 := ds_abs1.spi_abs1 with
TX_SHIFT_REG := (EL (ds_abs1.ds_abs1_tx.tx_cur_length - 1)
(ds_abs1.ds_abs1_tx.tx_data_buffer)) |>`

val spi_abs1_tx_last_update_op_def = Define `
spi_abs1_tx_last_update_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| state := abs1_tx_done_1;
spi_abs1 := ds_abs1.spi_abs1 with
TX_SHIFT_REG := (EL (ds_abs1.ds_abs1_tx.tx_cur_length - 1) 
(ds_abs1.ds_abs1_tx.tx_data_buffer)) |>`

val spi_abs1_tx_operations_def = Define `
spi_abs1_tx_operations (ds_abs1:ds_abs1_state) =
if (ds_abs1.state = abs1_tx_idle) then
(spi_abs1_tx_idle_op ds_abs1)
else if (ds_abs1.state = abs1_tx_data_1) then
(spi_abs1_tx_data_1_op ds_abs1)
else if (ds_abs1.state = abs1_tx_data_2) then
(spi_abs1_tx_data_2_op ds_abs1)
else if (ds_abs1.state = abs1_tx_update) then
(spi_abs1_tx_update_op ds_abs1)
else if (ds_abs1.state = abs1_tx_last_update) then
(spi_abs1_tx_last_update_op ds_abs1)
else ds_abs1 with err := T`


(* Other internal tx functions. *)
val comb_abs1_tx_trans_op_def = Define `
comb_abs1_tx_trans_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <| 
state := if ds_abs1.ds_abs1_tx.tx_cur_length < ((LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer) - 1)
then abs1_tx_data_2 else abs1_tx_data_1;
ds_abs1_tx := ds_abs1.ds_abs1_tx with tx_cur_length := ds_abs1.ds_abs1_tx.tx_cur_length + 1 |>`

val comb_abs1_tx_done_2_op_def = Define `
comb_abs1_tx_done_2_op (ds_abs1:ds_abs1_state) =
ds_abs1 with <|
state := if ds_abs1.ds_abs1_tx.tx_cur_length < ((LENGTH ds_abs1.ds_abs1_tx.tx_data_buffer) - 1)
then abs1_tx_next else abs1_tx_last;
ds_abs1_tx := ds_abs1.ds_abs1_tx with tx_cur_length := ds_abs1.ds_abs1_tx.tx_cur_length + 1 |>`

val comb_abs1_tx_reset_op_def = Define `
comb_abs1_tx_reset_op (ds_abs1:ds_abs1_state) =
ds_abs1 with state := abs1_ready`

val comb_abs1_tx_operations_def = Define `
comb_abs1_tx_operations (ds_abs1:ds_abs1_state) =
if ds_abs1.state = abs1_tx_trans 
then (comb_abs1_tx_trans_op ds_abs1)
else if ds_abs1.state = abs1_tx_done_2 
then (comb_abs1_tx_done_2_op ds_abs1)
else if ds_abs1.state = abs1_tx_reset 
then (comb_abs1_tx_reset_op ds_abs1)
else ds_abs1 with err := T`

(* ABS1_TX_LBL_ENABLE: ds_abs1 is permitted to transmit a byte. *)
val ABS1_TX_LBL_ENABLE_def = Define `
ABS1_TX_LBL_ENABLE (ds_abs1:ds_abs1_state) =
((ds_abs1.state = abs1_tx_done_1) \/
(ds_abs1.state = abs1_tx_done_2) \/
(ds_abs1.state = abs1_tx_next) \/
(ds_abs1.state = abs1_tx_last))`

val abs1_tx_trans_done_op_def = Define `
abs1_tx_trans_done_op (ds_abs1:ds_abs1_state) =
if ds_abs1.state = abs1_tx_done_1 then
(ds_abs1 with state := abs1_tx_reset,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else if ds_abs1.state = abs1_tx_done_2 then
(ds_abs1 with state := abs1_tx_trans,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else if ds_abs1.state = abs1_tx_next then
(ds_abs1 with state := abs1_tx_update,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else if ds_abs1.state = abs1_tx_last then
(ds_abs1 with state := abs1_tx_last_update,
SOME ds_abs1.spi_abs1.TX_SHIFT_REG)
else (ds_abs1 with err := T, NONE)`

val abs1_tx_trans_done_op_value_def = Define `
abs1_tx_trans_done_op_value (ds_abs1:ds_abs1_state) =
let (ds_abs1', v) = (abs1_tx_trans_done_op ds_abs1)
in v`

val abs1_tx_trans_done_op_state_def = Define `
abs1_tx_trans_done_op_state (ds_abs1:ds_abs1_state) =
let (ds_abs1', v) = (abs1_tx_trans_done_op ds_abs1)
in ds_abs1'`

(* call_tx_ds_abs1: call ds_abs1 to apply tx mode. *)
val call_tx_ds_abs1_def = Define `
call_tx_ds_abs1 (ds_abs1:ds_abs1_state) (buffer:word8 list) =
ds_abs1 with <| ds_abs1_tx := ds_abs1.ds_abs1_tx with 
<| tx_data_buffer := buffer; tx_cur_length := 0 |>;
state := abs1_tx_idle |>`

val _ = export_theory();
