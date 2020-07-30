open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_tx";

(* SPI controller operations when channel 0 is enabled for tx.
 * tx_channel_enabled_op: spi_state -> spi_state
 *)
val tx_channel_enabled_op_def = Define `
tx_channel_enabled_op (spi:spi_state) =
spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT 
with TXS := 1w; (* TXS is set to 1 when enable channel 0 *)
tx := spi.tx with state := tx_ready_for_trans |>`

(* SPI controller's operation if it starts to transmit data. 
 * TX0 -> TX_SHIFT_REG, SPI internal data transition.
 * tx_trans_data_op: spi_state -> spi_state 
 *)
val tx_trans_data_op_def = Define `
tx_trans_data_op (spi:spi_state) =
spi with <| TX_SHIFT_REG := w2w spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <|EOT := 0w; TXS := 1w|>; (* EOT bit is cleared, TXS bit is set*)  
tx := spi.tx with state := tx_trans_done |>`

(* SPI controller's operation when the data is transferred to another SPI device.
 * It's not the SPI internal operation, but depends on SPI slave's state.
 * master TX_SHIFT_REG -> slave RX_SHIFT_REG, shows the interactions between master and slave.
 * tx_trans_done_op: spi_state -> spi_state -> spi_state * word8 option
 *)
val tx_trans_done_op_def = Define `
tx_trans_done_op (spi:spi_state) (spi':spi_state) =
if (spi.tx.state = tx_trans_done) /\ (spi'.rx.state = rx_receive_data) /\ (spi'.regs.CH0STAT.RXS = 0w) then
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
(* An SPI word is transferred from the TX shift register to the slave *)
with EOT := 1w;
tx := spi.tx with state := tx_trans_check|>,
SOME spi.TX_SHIFT_REG)
else (spi, NONE)`

(* SPI controller's operation after EOT bit is set to 1.
 * tx_trans_check_op: spi_state -> spi_state
 *)
val tx_trans_check_op_def = Define `
tx_trans_check_op (spi:spi_state) = 
if (CHECK_TXS_BIT spi) /\ (CHECK_EOT_BIT spi) then
spi with tx := spi.tx with state := tx_ready_for_trans
else spi with err := T`

(* This function indicates SPI controller's internal operations for tx automaton.
 * spi_tx_operations: spi_state -> spi_state -> spi_state * word8 option
 *)
val spi_tx_operations_def = Define `
spi_tx_operations (spi:spi_state) =
case spi.tx.state of
  | tx_idle => spi with err := T
  | tx_conf_ready => spi with err := T
  | tx_channel_enabled => tx_channel_enabled_op spi 
  | tx_ready_for_trans => spi with err := T
  | tx_trans_data => tx_trans_data_op spi
  | tx_trans_done => spi with err := T
  | tx_trans_check => tx_trans_check_op spi
  | tx_channel_disabled => spi with err := T`

val _ = export_theory();
