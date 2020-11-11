open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory driver_stateTheory;

(* ds_abs1: driver and spi controller combined abstract model (level1) states.
 * This abstract model removes the interactions of the driver and spi controller, 
 * including Write/Update, Read/Return.
 * We assume that the driver model commands are correct considering the spi model.
 *)
val _ = new_theory "ds_abs1_state";

(* ds_abs1_init_state: the state of ds_abs1 init automaton *)
val _ = Datatype `ds_abs1_init_general_state =
| abs1_init_pre | abs1_init_start | abs1_init_check | abs1_init_done`

val _ = Datatype `ds_abs1_init_state = <|
state : ds_abs1_init_general_state |>`

(* ds_abs1_tx_state: the state of ds_abs1 tx automaton *)
val _ = Datatype `ds_abs1_tx_general_state =
| abs1_tx_pre | abs1_tx_idle | abs1_tx_prepare | abs1_tx_trans 
| abs1_tx_done_1 | abs1_tx_done_2 | abs1_tx_done_3
| abs1_tx_check_1 | abs1_tx_check_2 | abs1_tx_check_3 
| abs1_tx_next | abs1_tx_ready_for_reset | abs1_tx_reset`

val _ = Datatype `ds_abs1_tx_state = <|
state: ds_abs1_tx_general_state;
tx_data_buffer: word8 list;
tx_left_length: num |>`

(* ds_abs1_rx_state: the state of ds_abs1 rx automaton *)
val _ = Datatype `ds_abs1_rx_general_state =
| abs1_rx_pre | abs1_rx_idle | abs1_rx_receive | abs1_rx_update
| abs1_rx_ready | abs1_rx_fetch_data | abs1_rx_return | abs1_rx_done
| abs1_rx_ready_for_reset | abs1_rx_reset`

val _ = Datatype `ds_abs1_rx_state = <|
state: ds_abs1_rx_general_state;
rx_data_buffer: word8 list;
rx_left_length: num |>`

(* ds_abs1_xfer_state: the state of ds_abs1 xfer automaton *)
val _ = Datatype `ds_abs1_xfer_general_state =
| abs1_xfer_pre | abs1_xfer_idle | abs1_xfer_prepare | abs1_xfer_trans
| abs1_xfer_exchange | abs1_xfer_update | abs1_xfer_ready | abs1_xfer_fetch_data
| abs1_xfer_next | abs1_xfer_next_write | abs1_xfer_done
| abs1_xfer_ready_for_reset | abs1_xfer_reset`

val _ = Datatype `ds_abs1_xfer_state = <|
state: ds_abs1_xfer_general_state;
xfer_dataIN_buffer: word8 list;
xfer_dataOUT_buffer: word8 list;
xfer_left_length: num |>`

val _ = Datatype `spi_abs1_state = <|
TX_SHIFT_REG: word8;
RX_SHIFT_REG: word8 |>`

(* TO REMOVE*)
val _ = Datatype `driver_abs1_state = <|
dr_abs1_last_read_ad: word32 option;
dr_abs1_last_read_v: word32 option |>`

(* ds_abs1_state: the state of the spi controller and driver combined abstract level1 model *)
val _ = Datatype `ds_abs1_state = <|
err: bool;
spi_abs1: spi_abs1_state;
driver_abs1: driver_abs1_state; (* TO REMOVE*)
ds_abs1_init: ds_abs1_init_state;
ds_abs1_tx: ds_abs1_tx_state;
ds_abs1_rx: ds_abs1_rx_state;
ds_abs1_xfer: ds_abs1_xfer_state |>`

val _ = Datatype `abs1_lbl_type =
| tau_comb | tau_dr | tau_spi`

val _ = export_theory();
