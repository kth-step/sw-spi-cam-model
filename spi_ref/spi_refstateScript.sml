open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory;

(* SPI_ref model states *)
val _ = new_theory "spi_refstate";

(* spi_ref controller initialization automaton *)
val _ = Datatype `ref_init_general_state = 
| ref_init_start | ref_init_setregs | ref_init_done`

val _ = Datatype `ref_init_state = <|
state: ref_init_general_state;
sysconfig_mode_done: bool;
modulctrl_bus_done: bool;
ch0conf_wordlen_done: bool;
ch0conf_mode_done: bool;
ch0conf_speed_done: bool |>`

(* spi_ref controller transmit automaton *)
val _ = Datatype `ref_tx_general_state =
| ref_tx_idle | ref_tx_conf_ready | ref_tx_ready_for_trans
| ref_tx_trans_done | ref_tx_channel_disabled`

val _ = Datatype `ref_tx_state = <|
state: ref_tx_general_state |>`

(* spi_ref controller receive automaton *)
val _ = Datatype `ref_rx_general_state =
| ref_rx_idle | ref_rx_conf_ready | ref_rx_receive_data 
| ref_rx_data_ready | ref_rx_channel_disabled`

val _ = Datatype `ref_rx_state = <|
state: ref_rx_general_state |>`

(* spi_ref controller transfer automaton (full-dulplex mode) *)
val _ = Datatype `ref_xfer_general_state =
| ref_xfer_idle | ref_xfer_conf_ready | ref_xfer_ready_for_trans
| ref_xfer_exchange_data | ref_xfer_data_ready | ref_xfer_channel_disabled`

val _ = Datatype `ref_xfer_state = <|
state : ref_xfer_general_state |>`

(* spi_ref controller model state*)
val _ = Datatype `spi_ref_state = <|
err: bool;
regs: spi_regs;
TX_SHIFT_REG : word8;
RX_SHIFT_REG : word8;
init: ref_init_state;
tx: ref_tx_state;
rx: ref_rx_state;
xfer: ref_xfer_state |>`

val _ = export_theory();
