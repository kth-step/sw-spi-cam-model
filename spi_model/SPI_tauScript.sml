open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_tau";

(* SPI_TAU_ENABLE: SPI is in a state that can perform tau transition. *)
val SPI_TAU_ENABLE_def = Define `
SPI_TAU_ENABLE (spi:spi_state) =
((spi.state = init_reset) \/ (spi.state = tx_channel_enabled) \/
(spi.state = tx_trans_data) \/ (spi.state = tx_trans_update) \/
(spi.state = rx_channel_enabled) \/ (spi.state = rx_update_RX0) \/ 
(spi.state = xfer_channel_enabled) \/ (spi.state = xfer_trans_data) \/ 
(spi.state = xfer_update_RX0))`

(* internal operations for init automaton *)
(* SPI controller performs reset operation. *)
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with <| regs := spi.regs with <|SYSSTATUS := 1w (* indiciate reset is done *);
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w |> |>;
state := init_setregs (* enter the next init state, set up SPI registers *) |>`

(* internal operations for tx automaton *)
(* SPI controller internal operation when the channel is enabled for tx. *)
val tx_channel_enabled_op_def = Define `
tx_channel_enabled_op (spi:spi_state) =
spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT 
with <| EOT := 1w; TXS := 1w |>;
state := tx_ready_for_trans |>`

(* tx_trans_data_op: after TX0 register was set, SPI uploads the data from TX0 to TX_SHIFT_REG. *)
val tx_trans_data_op_def = Define `
tx_trans_data_op (spi:spi_state) =
spi with <| TX_SHIFT_REG := w2w spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| EOT := 0w; TXS := 1w|>; (* cleat EOT bit, set TXS *)  
state := tx_trans_done |>`

(* tx_trans_update_op: similiar with tx_trans_data_op *)
val tx_trans_update_op_def = Define `
tx_trans_update_op (spi:spi_state) =
spi with <| TX_SHIFT_REG := w2w spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| EOT := 0w; TXS := 1w|>;
state := tx_trans_done |>`

(* internal operations for rx automaton *)
(* rx_channel_enabled_op: SPI controller internal operation when the channel is enabled for rx mode. *)
val rx_channel_enabled_op_def = Define `
rx_channel_enabled_op (spi:spi_state) =
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with RXS := 0w (* RXS is cleared when enable the channel *);
state := rx_receive_data |>`

(* rx_update_RX0_op: SPI uploads the data from the RX_SHIFT register to the RX0 register. *)
val rx_update_RX0_op_def = Define `
rx_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* a received word is transferred from shift register to RX0 *)
<| RX0 := w2w spi.RX_SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
state := rx_data_ready |>`

(* internal operations for xfer automaton *)
(* xfer_channel_enabled_op: SPI controller internal operation when the channel is enabled for xfer mode. *)
val xfer_channel_enabled_op_def = Define `
xfer_channel_enabled_op (spi:spi_state) = 
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| RXS := 0w; TXS := 1w |>;
state := xfer_ready_for_trans |>`

(* xfer_trans_data_op: upload the data from TX0 to the TX_SHIFT_REG after TX0 was written. *)
val xfer_trans_data_op_def = Define `
xfer_trans_data_op (spi:spi_state) =
spi with <| (* TX0 -> TX_shift_register *)
TX_SHIFT_REG := w2w spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| EOT := 0w; TXS := 1w |>;
state := xfer_exchange_data |>`

(* xfer_update_RX0_op: SPI controller handles the received word from shift register to RX0. *)
val xfer_update_RX0_op_def = Define `
xfer_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* shift register -> RX0 *)
<| RX0 := w2w spi.RX_SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
state := xfer_data_ready |>`

(* This function shows internal operations of SPI controller. *)
val spi_tau_operations_def = Define `
spi_tau_operations (spi:spi_state) =
case spi.state of
  | init_start => spi with err := T
  | init_reset => init_reset_op spi
  | init_setregs => spi with err := T
  | spi_ready => spi with err := T
  | tx_conf_ready => spi with err := T
  | tx_channel_enabled => tx_channel_enabled_op spi
  | tx_ready_for_trans => spi with err := T
  | tx_trans_data => tx_trans_data_op spi
  | tx_trans_done => spi with err := T
  | tx_trans_next => spi with err := T
  | tx_trans_update => tx_trans_update_op spi
  | tx_channel_disabled => spi with err := T
  | rx_conf_ready => spi with err := T
  | rx_channel_enabled => rx_channel_enabled_op spi
  | rx_receive_data => spi with err := T
  | rx_update_RX0 => rx_update_RX0_op spi
  | rx_data_ready => spi with err := T
  | rx_channel_disabled => spi with err := T
  | xfer_conf_ready => spi with err := T
  | xfer_channel_enabled => xfer_channel_enabled_op spi
  | xfer_ready_for_trans => spi with err := T
  | xfer_trans_data => xfer_trans_data_op spi
  | xfer_exchange_data => spi with err := T
  | xfer_update_RX0 => xfer_update_RX0_op spi
  | xfer_data_ready => spi with err := T
  | xfer_channel_disabled => spi with err :=T`

val _ = export_theory();
