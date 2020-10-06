open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory;

(* SPI_abs model states *)
val _ = new_theory "spi_absstate";

(* spi_abs controller initialization automaton *)
val _ = Datatype `abs_init_general_state = 
| abs_init_start | abs_init_setregs | abs_init_done`

val _ = Datatype `abs_init_state = <|
state: abs_init_general_state;
sysconfig_mode_done: bool;
modulctrl_bus_done: bool;
ch0conf_wordlen_done: bool;
ch0conf_mode_done: bool;
ch0conf_speed_done: bool |>`

(* spi_abs controller transmit automaton *)
val _ = Datatype `abs_tx_general_state =
| abs_tx_idle | abs_tx_conf_ready | abs_tx_ready_for_trans
| abs_tx_trans_done | abs_tx_channel_disabled`

val _ = Datatype `abs_tx_state = <|
state: abs_tx_general_state |>`

(* spi_abs controller receive automaton *)
val _ = Datatype `abs_rx_general_state =
| abs_rx_idle | abs_rx_conf_ready | abs_rx_receive_data 
| abs_rx_data_ready | abs_rx_channel_disabled`

val _ = Datatype `abs_rx_state = <|
state: abs_rx_general_state |>`

(* spi_abs controller transfer automaton (full-dulplex mode) *)
val _ = Datatype `abs_xfer_general_state =
| abs_xfer_idle | abs_xfer_conf_ready | abs_xfer_ready_for_trans
| abs_xfer_exchange_data | abs_xfer_data_ready | abs_xfer_channel_disabled`

val _ = Datatype `abs_xfer_state = <|
state : abs_xfer_general_state |>`

(* spi_abs controller model state*)
val _ = Datatype `spi_abs_state = <|
err: bool;
regs: spi_regs;
TX_SHIFT_REG : word8;
RX_SHIFT_REG : word8;
init: abs_init_state;
tx: abs_tx_state;
rx: abs_rx_state;
xfer: abs_xfer_state |>`

val _ = export_theory();
