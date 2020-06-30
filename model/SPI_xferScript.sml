open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory;

val _ = new_theory "SPI_xfer";

(* xfer_channel_enabled_op:spi_state -> spi_state *)
val xfer_channel_enabled_op_def = Define `
xfer_channel_enabled_op (spi:spi_state) = 
spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <|RXS := 1w ;TXS := 1w|>;
xfer := spi.xfer with state := xfer_issue_mem_req |>`

(* xfer_issue_mem_req_op: spi_state -> spi_state * mem_req option *)
val xfer_issue_mem_req_op_def = Define `
xfer_issue_mem_req_op (spi:spi_state) =
let req = <|pa := spi.xfer.tx_buffer_pa; v := NONE|> in
if (CHECK_TXS_BIT spi) /\ (BUFFER_IN_BOARD_RAM spi.xfer.tx_buffer_pa spi.xfer.left_length) 
then (spi with xfer := spi.xfer with <|state := xfer_mem_reply;
tx_buffer_pa := spi.xfer.tx_buffer_pa + 1w |>, SOME req)
else (spi with err := T, NONE)`

(* xfer_mem_reply_op:spi_state -> mem_req -> spi_state *)
val xfer_mem_reply_op_def = Define `
xfer_mem_reply_op (spi:spi_state) (req:mem_req) =
spi with <|regs := spi.regs with TX0 := THE req.v; 
xfer := spi.xfer with state := xfer_issue_write_mem_req|>`

(* xfer_issue_write_mem_req_op: spi_state -> spi_state * mem_req option *)
val xfer_issue_write_mem_req_op_def = Define `
xfer_issue_write_mem_req_op (spi:spi_state) =
let req = <|pa := spi.xfer.rx_buffer_pa; v := SOME (spi.regs.RX0)|> in
if (CHECK_RXS_BIT spi) /\ (BUFFER_IN_BOARD_RAM spi.xfer.rx_buffer_pa spi.xfer.left_length) 
then (spi with xfer := spi.xfer with <| state := xfer_check;
rx_buffer_pa := spi.xfer.rx_buffer_pa + 1w;
left_length := spi.xfer.left_length - 1 |>, SOME req)
else (spi with err := T, NONE)`

(* xfer_check_op: spi_state -> spi_state *)
val xfer_check_op_def = Define `
xfer_check_op (spi:spi_state) =
if (spi.xfer.left_length = 0) then
spi with xfer := spi.xfer with state := xfer_disable_channel
else spi with xfer := spi.xfer with state := xfer_issue_mem_req`

(* The xfer_operations indicates SPI hardware internel operations
   based on the xfer.state: spi_state -> spi_state * mem_req option *)
val xfer_operations_def = Define `
xfer_operations (spi:spi_state) =
case spi.xfer.state of
  | xfer_idle => (spi with err := T, NONE)
  | xfer_conf_ready => (spi with err := T, NONE)
  | xfer_channel_enabled => (xfer_channel_enabled_op spi, NONE)
  | xfer_issue_mem_req => xfer_issue_mem_req_op spi
  | xfer_mem_reply => (spi with err := T, NONE)
  | xfer_issue_write_mem_req => xfer_issue_write_mem_req_op spi
  | xfer_check => (xfer_check_op spi, NONE)
  | xfer_disable_channel => (spi with err := T, NONE)
  | xfer_reset_conf => (spi with err := T, NONE)`

val _ = export_theory();
