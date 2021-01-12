open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;

(* ds_abs0: a more abstract model for the SPI driver and controller than ds_abs1.
 * This abstract model removes all tau transitions in the combined model.
 *)
val _ = new_theory "ds_abs0_state";

(* ds_abs0_general_state: the general states of ds_abs0 *)
val _ = Datatype `ds_abs0_general_state =
| abs0_init | abs0_ready
| abs0_tx 
| abs0_rx_idle | abs0_rx_update | abs0_rx_reading | abs0_rx_next
| abs0_xfer_idle | abs0_xfer_done`

(* ds_abs0_tx_state: the state of ds_abs0 tx automaton *)
val _ = Datatype `ds_abs0_tx_state = <| 
tx_data_buffer: word8 list;
tx_cur_length: num |>`

(* ds_abs0_rx_state: the state of ds_abs0 rx automaton *)
val _ = Datatype `ds_abs0_rx_state = <|
rx_data_buffer: word8 list;
rx_left_length: num;
temp_value: word8 |>`

(* ds_abs0_xfer_state: the state of ds_abs0 xfer automaton *)
val _ = Datatype `ds_abs0_xfer_state = <|
xfer_dataIN_buffer: word8 list;
xfer_dataOUT_buffer: word8 list;
xfer_cur_length: num |>`

(* ds_abs0_state: the state of the spi controller and driver combined abstract level0 model *)
val _ = Datatype `ds_abs0_state = <|
err: bool;
state: ds_abs0_general_state;
ds_abs0_tx: ds_abs0_tx_state;
ds_abs0_rx: ds_abs0_rx_state;
ds_abs0_xfer: ds_abs0_xfer_state |>`

val _ = export_theory();