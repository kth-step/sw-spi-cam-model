open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory;

val _ = new_theory "SPI_tx";

(* tx_channel_enabled_op: spi_state -> spi_state *)
val tx_channel_enabled_op_def = Define `
tx_channel_enabled_op (spi:spi_state) =
spi with <| regs:=spi.regs with CH0STAT := spi.regs.CH0STAT 
with <|RXS := 0w; TXS := 1w|>; (* RXS and TXS are set when enable channel *)
tx := spi.tx with state := tx_issue_mem_req |>`

(* tx_issue_mem_req_op: spi_state -> spi_state * mem_req option *)
val tx_issue_mem_req_op_def = Define `
tx_issue_mem_req_op (spi:spi_state) =
let req = <|pa := spi.tx.tx_buffer_pa; v := NONE|> in
if (CHECK_TXS_BIT spi) /\ (BUFFER_IN_BOARD_RAM spi.tx.tx_buffer_pa spi.tx.tx_left_length) 
then (spi with tx := spi.tx with  <|state := tx_mem_reply; (* waiting for memory reply *)
tx_buffer_pa := spi.tx.tx_buffer_pa + 1w; (* go to next pa *)
tx_left_length := spi.tx.tx_left_length - 1 (* left_length-- *)|>, SOME req)
else (spi with err := T, NONE)`

(* TX_NO_LEFT_LENGTH: tx_state -> bool *)
val TX_NO_LEFT_BYTES_def = Define `
TX_NO_LEFT_BYTES (txs:tx_state) = (txs.tx_left_length = 0)`

(* tx_mem_reply_op: spi_state -> mem_req -> spi_state *)
val tx_mem_reply_op_def = Define `
tx_mem_reply_op (spi:spi_state) (req:mem_req) =
if TX_NO_LEFT_BYTES spi.tx then
spi with <|regs := spi.regs with TX0 := THE req.v; tx := spi.tx with state := tx_done|>
else 
spi with <|regs := spi.regs with TX0 := THE req.v; tx := spi.tx with state := tx_issue_mem_req|>`

(* tx_done_op: spi_state -> spi_state *)
val tx_done_op_def = Define `
tx_done_op (spi:spi_state) = 
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <|TXS := 1w; EOT := 1w|>;
tx := spi.tx with state := tx_disable_channel |>`

(* The tx_operations indicates SPI hardware internal operations 
   based on the tx.state: spi_state -> spi_state * mem_req option *)
val tx_operations_def = Define `
tx_operations (spi:spi_state) =
case spi.tx.state of
  | tx_idle => (spi with err := T, NONE)
  | tx_conf_ready => (spi with err:= T, NONE)
  | tx_channel_enabled => (tx_channel_enabled_op spi, NONE) 
  | tx_issue_mem_req => tx_issue_mem_req_op spi
  | tx_mem_reply => (spi with err := T, NONE)
  | tx_done => (tx_done_op spi, NONE)
  | tx_disable_channel => (spi with err := T, NONE)
  | tx_reset_conf => (spi with err := T, NONE)`

val _ = export_theory();
