open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory driver_stateTheory;

(* ds_abs1: SPI driver and controller combined abstract model (level 1). *)
val _ = new_theory "ds_abs1_state";

(* ds_abs1_general_state: the general states of ds_abs1 model *)
val _ = Datatype `ds_abs1_general_state =
| abs1_init_pre | abs1_init_start | abs1_ready
| abs1_tx_idle | abs1_tx_trans | abs1_tx_data_1 | abs1_tx_data_2
| abs1_tx_done_1 | abs1_tx_done_2 | abs1_tx_next | abs1_tx_update 
| abs1_tx_last | abs1_tx_last_update | abs1_tx_reset
| abs1_rx_idle | abs1_rx_receive | abs1_rx_update | abs1_rx_ready | abs1_rx_read
| abs1_rx_fetch_data | abs1_rx_next | abs1_rx_next_ready | abs1_rx_reset
| abs1_xfer_idle | abs1_xfer_prepare | abs1_xfer_data | abs1_xfer_exchange 
| abs1_xfer_update | abs1_xfer_ready | abs1_xfer_fetch_data | abs1_xfer_reset`

(* ds_abs1_tx_state: the state of ds_abs1 tx automaton *)
val _ = Datatype `ds_abs1_tx_state = <|
tx_data_buffer: word8 list;
tx_cur_length: num |>`

(* ds_abs1_rx_state: the state of ds_abs1 rx automaton *)
val _ = Datatype `ds_abs1_rx_state = <|
rx_data_buffer: word8 list;
rx_left_length: num;
temp_value: word8 |>`

(* ds_abs1_xfer_state: the state of ds_abs1 xfer automaton *)
val _ = Datatype `ds_abs1_xfer_state = <|
xfer_dataIN_buffer: word8 list;
xfer_dataOUT_buffer: word8 list;
xfer_cur_length: num |>`

val _ = Datatype `spi_abs1_state = <|
TX_SHIFT_REG: word8;
RX_SHIFT_REG: word8 |>`

(* ds_abs1_state: the state of ds_abs1 model *)
val _ = Datatype `ds_abs1_state = <|
err: bool;
state: ds_abs1_general_state;
spi_abs1: spi_abs1_state;
ds_abs1_tx: ds_abs1_tx_state;
ds_abs1_rx: ds_abs1_rx_state;
ds_abs1_xfer: ds_abs1_xfer_state |>`

(* some labels to describe ds_abs1 internal operations *)
val _ = Datatype `abs1_lbl_type =
| tau_comb | tau_dr | tau_spi`

val _ = export_theory();
