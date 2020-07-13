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

(* SPI controller's operation if it starts to transmit data. (TX0 -> shift Reg)
 * tx_trans_data_op: spi_state -> spi_state 
 *)
val tx_trans_data_op_def = Define `
tx_trans_data_op (spi:spi_state) =
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
(* Data is transferred from TX0 to the shift register (the wire) *)
with <|EOT := 0w; TXS := 1w|>;  
tx := spi.tx with state := tx_trans_done |>`

(* SPI controller's operation when the data 
 * is transferred to the slave over the wire. (shift Reg -> slave)
 * tx_trans_done_op: spi_state -> spi_state
 *)
val tx_trans_done_op_def = Define `
tx_trans_done_op (spi:spi_state) =
spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
(* An SPI word is transferred from the shift register to the slave *)
with EOT := 1w;
tx := spi.tx with state := tx_trans_check |>`

(* CHECK_EOT_BIT_def: spi_state -> bool *)
val CHECK_EOT_BIT_def = Define `
CHECK_EOT_BIT (spi:spi_state) = (spi.regs.CH0STAT.EOT = 1w)`

(* SPI controller's operation after EOT bit is set to 1.
 * tx_trans_check_op: spi_state -> spi_state
 *)
val tx_trans_check_op_def = Define `
tx_trans_check_op (spi:spi_state) = 
if (CHECK_TXS_BIT spi) /\ (CHECK_EOT_BIT spi) then
spi with tx := spi.tx with state := tx_ready_for_trans
else spi with err := T`

(* This function indicates SPI controller's internal operations for tx automaton.
 * spi_tx_operations: spi_state -> spi_state 
 *)
val spi_tx_operations_def = Define `
spi_tx_operations (spi:spi_state) =
case spi.tx.state of
  | tx_idle => spi with err := T
  | tx_conf_ready => spi with err := T
  | tx_channel_enabled => tx_channel_enabled_op spi 
  | tx_ready_for_trans => spi with err := T
  | tx_trans_data => tx_trans_data_op spi
  | tx_trans_done => tx_trans_done_op spi
  | tx_trans_check => tx_trans_check_op spi
  | tx_channel_disabled => spi with err := T`


val _ = export_theory();
