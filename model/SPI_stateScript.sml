open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory board_memTheory;

val _ = new_theory "SPI_state";

(* SPI initialization *)
val _ = Datatype `init_general_state = 
| init_start | init_reset | init_setregs | init_done`

val _ = Datatype `init_state = <|
state: init_general_state;
sysconfig_mode_done: bool;
modulctrl_bus_done: bool;
ch0conf_wordlen_done: bool;
ch0conf_mode_done: bool;
ch0conf_speed_done: bool |>`

(* SPI transmit *)
val _ = Datatype `tx_general_state =
| tx_idle | tx_conf_ready | tx_channel_enabled | tx_issue_mem_req
| tx_mem_reply | tx_done | tx_disable_channel | tx_reset_conf`

val _ = Datatype `tx_state = <|
state: tx_general_state;
tx_buffer_pa: word32;
tx_left_length: num |>`

(* SPI receive *)
val _ = Datatype `rx_general_state =
| rx_idle | rx_conf_ready | rx_channel_enabled | rx_issue_write_mem_req
| rx_check | rx_disable_channel | rx_reset_conf`

val _ = Datatype `rx_state = <|
state: rx_general_state;
rx_buffer_pa : word32;
rx_left_length: num |>`

(* SPI transmit and receive, full-dulplex *)
val _ = Datatype `xfer_general_state =
| xfer_idle | xfer_conf_ready | xfer_channel_enabled | xfer_issue_mem_req
| xfer_mem_reply | xfer_issue_write_mem_req | xfer_check
| xfer_disable_channel | xfer_reset_conf`

val _ = Datatype `xfer_state = <|
state : xfer_general_state;
tx_buffer_pa : word32;
rx_buffer_pa : word32;
left_length : num |>`

(* SPI registers, only related registers and bits are included. *)
(* Bits in SYSCONFIG register *)
val _ = Datatype `sysconfig_bits = <|
SIDLEMODE: word2; (* smart-idle mode *)
SOFTRESET: word1; (* Software reset *)
AUTOIDLE: word1 (* Internal OCP clock gating strategy *) |>`

(* Bits in MODULCTRL register *)
val _ = Datatype `modulctrl_bits = <|
SYSTEM_TEST: word1; (* Enable system test mode *)
MS: word1; (* Master/Slave *)
SINGLE: word1 (* Single/multi channel, master mode only *)|>`

(* Bits in CH0CONF register *)
val _ = Datatype `ch0conf_bits = <|
PHA: word1; (* SPICLK phase *)
POL: word1; (* SPICLK polarity *)
CLKD: word4; (* Frequency divider for SPICLK, only when master mode *)
EPOL: word1; (* SPIEN polarity *)
WL: word5; (* SPI word length *)
TRM: word2; (* Transmit/receive mode *)
DPE0: word1; (* Transmission enable for data line 0 *)
DPE1: word1; (* Transmission enable for data line 1 *)
IS: word1; (* Input select *)
TURBO: word1; (* Turbo mode *)
FORCE: word1 (* Manual SPIEN assertion to keep SPIEN active between SPI words *) |>`

(* Bits in CH0STAT register *)
val _ = Datatype `ch0stat_bits = <|
RXS: word1; (* Channel 0 receiver register status *)
TXS: word1; (* Channel 0 transmitter register status *)
EOT: word1  (* Channel 0 end-of-transfer status *) |>`

val _ = Datatype `spi_regs = <|
SYSCONFIG: sysconfig_bits;
SYSSTATUS: word1;
MODULCTRL: modulctrl_bits;
CH0CONF: ch0conf_bits;
CH0STAT: ch0stat_bits;
CH0CTRL: word1;
TX0: word8;
RX0: word8 |>`

(* SPI bus state *)
val _ = Datatype `spi_state = <|
err: bool; (* SPI bus is in an error state or not *)
regs: spi_regs; (* SPI registers value *)
init: init_state; (* initialization state *)
tx: tx_state; (* transmit state *)
rx: rx_state; (* receive state *)
xfer: xfer_state (* transfer (transmit and receive) state *) |>`

val _ = Datatype `mem_req = <|
pa: word32;
v: word8 option |>`

(* shcedule automaton indicates the status of SPI bus *)
val _ = Datatype `schedule = | Initialize | Transmit | Receive | Transfer`

(* Externel environment connected to the SPI bus *)
val _ = Datatype `environment = <|
scheduler : schedule;
read_reg : word32 |>`

(* CHECK_RXS_BIT_def: spi_state -> bool *)
val CHECK_RXS_BIT_def = Define `
CHECK_RXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.RXS = 1w)`

(* CHECK_TXS_BIT_def: spi_state -> bool *)
val CHECK_TXS_BIT_def = Define `
CHECK_TXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.TXS = 1w)`

(* CHECK if the buffer is in the RAM region: word32 -> num -> bool *)
val BUFFER_IN_BOARD_RAM_def = Define `
BUFFER_IN_BOARD_RAM (buffer_pa:word32) (left_length:num) =
let start_pa = buffer_pa
and length = n2w left_length: word32
in !a. a <+ length ==> 
((BOARD_RAM_START <=+ start_pa + a) /\ (start_pa + a <+ BOARD_RAM_END))`

val _ = export_theory();
