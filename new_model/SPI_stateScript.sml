open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open board_memTheory;

val _ = new_theory "SPI_state";

(* spi_state, the SPI controller's state that contains registers, 
   an error flag and automaton's states *)

(* SPI registers, only related registers and bits are included. *)
(* Bits in SYSCONFIG register *)
val _ = Datatype `sysconfig_bits = <|
SIDLEMODE: word2; (* Smart-idle mode *)
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
CLKD: word4; (* Frequency divider for SPICLK, only valid in master mode *)
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

(* SPI registers *)
val _ = Datatype `spi_regs = <|
SYSCONFIG: sysconfig_bits; (* system configuration register *)
SYSSTATUS: word1; (* system status register *)
MODULCTRL: modulctrl_bits; (* module control register *)
CH0CONF: ch0conf_bits; (* channel 0 configuration register *)
CH0STAT: ch0stat_bits; (* channel 0 status register *)
CH0CTRL: word1; (* channel 0 control register *)
TX0: word32; (* channel 0 transmit buffer register *)
RX0: word32 (*channel 0 receive buffer register *)|>`

(* spi controller initialization automaton *)
val _ = Datatype `init_general_state = 
| init_start | init_reset | init_setregs | init_done`

val _ = Datatype `init_state = <|
state: init_general_state;
sysconfig_mode_done: bool;
modulctrl_bus_done: bool;
ch0conf_wordlen_done: bool;
ch0conf_mode_done: bool;
ch0conf_speed_done: bool |>`

(* spi controller transmit automaton *)
val _ = Datatype `tx_general_state =
| tx_idle | tx_conf_ready | tx_channel_enabled | tx_ready_for_trans
| tx_trans_data | tx_trans_done | tx_trans_check | tx_channel_disabled`

val _ = Datatype `tx_state = <|
state: tx_general_state |>`

(* spi controller receive automaton *)
val _ = Datatype `rx_general_state =
| rx_idle | rx_conf_ready | rx_channel_enabled | rx_receive_data 
| rx_update_RX0 | rx_data_ready | rx_receive_check | rx_channel_disabled`

val _ = Datatype `rx_state = <|
state: rx_general_state |>`

(* spi controller transfer automaton (transmit and receive, full-dulplex mode) *)
val _ = Datatype `xfer_general_state =
| xfer_idle | xfer_conf_ready | xfer_channel_enabled | xfer_ready_for_trans
| xfer_trans_data | xfer_exchange_data | xfer_update_RX0 
| xfer_data_ready | xfer_check | xfer_channel_disabled`

val _ = Datatype `xfer_state = <|
state : xfer_general_state |>`

(* spi_state: spi controller state *)
val _ = Datatype `spi_state = <|
err: bool; (* an error flag for SPI state*)
regs: spi_regs; (* SPI registers *)
SHIFT_REG : word8; (* Shift register to transfer data, not memory-mapped SPI register *)
init: init_state; (* initialization state *)
tx: tx_state; (* transmit state *)
rx: rx_state; (* receive state *)
xfer: xfer_state (* transfer (transmit and receive) state *) |>`

(* TODO: SPI driver that issues memory request to SPI registers. *)
(* spi_driver, including buffer's physical address and length *)
val _ = Datatype `driver_tx = <|
tx_buffer_pa: word32;
tx_left_length: num |>`

val _ = Datatype `driver_rx = <|
rx_buffer_pa : word32;
rx_left_length: num |>`

val _ = Datatype `driver_xfer = <|
tx_buffer_pa : word32;
rx_buffer_pa : word32;
left_length : num |>`

(* spi_driver: spi driver state, including init, tx, rx and xfer's buffer information *)
val _ = Datatype `spi_driver = <|
d_tx: driver_tx;
d_rx: driver_rx;
d_xfer: driver_xfer |>`

(* mem_req: memory reuqest *)
val _ = Datatype `mem_req = <|
pa: word32;
v: word8 option |>`

(* shcedule automaton indicates the status of SPI controller *)
val _ = Datatype `schedule = | Initialize | Transmit | Receive | Transfer`

(* Externel environment connected to the SPI bus *)
val _ = Datatype `environment = <|
scheduler : schedule; (* SPI bus scheduler *)
SHIFT_REG: word8; (* Slave shift register *)
read_reg : word32 (* An arbitrary value *)|>`

(* Some simple functions related to the spi_state *)
(* check SPI register's RXS bit. CHECK_RXS_BIT_def: spi_state -> bool *)
val CHECK_RXS_BIT_def = Define `
CHECK_RXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.RXS = 1w)`

(* check SPI register's TXS bit. CHECK_TXS_BIT_def: spi_state -> bool *)
val CHECK_TXS_BIT_def = Define `
CHECK_TXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.TXS = 1w)`

(* check SPI register's EOT bit. CHECK_EOT_BIT_def: spi_state -> bool *)
val CHECK_EOT_BIT_def = Define `
CHECK_EOT_BIT (spi:spi_state) = (spi.regs.CH0STAT.EOT = 1w)`

(* CHECK if the buffer is in the board RAM region. BUFFER_IN_BOARD_RAM: word32 -> num -> bool *)
val BUFFER_IN_BOARD_RAM_def = Define `
BUFFER_IN_BOARD_RAM (buffer_pa:word32) (left_length:num) =
let start_pa = buffer_pa
and length = n2w left_length: word32
in !a. a <+ length ==> 
((BOARD_RAM_START <=+ start_pa + a) /\ (start_pa + a <+ BOARD_RAM_END))`

val _ = export_theory();
