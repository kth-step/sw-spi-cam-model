open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

(* This script defines receive automaton of SPI bus *)
(* Ning Dong, June 2020 *)
val _ = new_theory "SPI_rx";

(* rx_channel_enabled_op : spi_state -> spi_state *)
val rx_channel_enabled_op_def = Define `
rx_channel_enabled_op (spi:spi_state) =
spi with <| regs := spi.regs with <|CH0STAT := spi.regs.CH0STAT
with <| RXS := 1w (* 1 byte is received from the slave *); TXS := 1w|>; TX0 := (0w:word8)|>; 
rx := spi.rx with state := rx_issue_write_mem_req|>`

(* RX_CHECK_RXS_BIT_def: spi_state -> bool *)
val RX_CHECK_RXS_BIT_def = Define `
RX_CHECK_RXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.RXS = 1w)`

val RX_BUFFER_IN_BOARD_RAM_def = Define `
RX_BUFFER_IN_BOARD_RAM (rxs:rx_state) =
let start_pa = rxs.rx_buffer_pa
and length = n2w rxs.rx_left_length: word32
in !a. a <+ length ==> 
((BOARD_RAM_START <=+ start_pa + a) /\ (start_pa + a <+ BOARD_RAM_END))`

(* rx_issue_write_mem_req_op: spi_state -> spi_state * mem_req option *)
val rx_issue_write_mem_req_op_def = Define `
rx_issue_write_mem_req_op (spi:spi_state) =
let req = <|pa := spi.rx.rx_buffer_pa; v := SOME (spi.regs.RX0)|>
and 
spi = spi with rx := spi.rx with
<|state := rx_check;
rx_buffer_pa := spi.rx.rx_buffer_pa + 1w;
rx_left_length := spi.rx.rx_left_length - 1 |>
in 
if (RX_CHECK_RXS_BIT spi) /\ (RX_BUFFER_IN_BOARD_RAM spi.rx)
then (spi, SOME req)
else (spi with err := T, NONE)`

(* rx_check_op: spi_state -> mem_req -> spi_state *)
val rx_check_op_def = Define `
rx_check_op (spi:spi_state) =
if (spi.rx.rx_left_length = 0) then
spi with rx := spi.rx with state := rx_disable_channel
else
spi with rx := spi.rx with state := rx_issue_write_mem_req`

(* The rx_operations indicates SPI internel operations based on the rx_state.
   spi_state -> spi_state * mem_req option *)
val rx_operations_def = Define `
rx_operations (spi: spi_state) =
case spi.rx.state of
| rx_idle => (spi with err := T, NONE)
| rx_conf_ready => (spi with err := T, NONE)
| rx_channel_enabled => (rx_channel_enabled_op spi, NONE)
| rx_issue_write_mem_req => rx_issue_write_mem_req_op spi
| rx_check => (rx_check_op spi, NONE)
| rx_disable_channel => (spi with err := T, NONE)
| rx_reset_conf => (spi with err := T, NONE)`

val _ = export_theory ();
