open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;

(* This script defines states of SPI bus. *)
(* Ning Dong, June 2020. *)
val _ = new_theory "board_state";

(* SPI initialization *)
val _ = Datatype `init_general_state = 
| init_start | init_reset | init_setregs | init_done`

val _ = Datatype `init_state = <|
state: init_general_state;
sysconifg_mode_done: bool;
modulctrl_bus_done: bool;
ch0conf_wordlen_done: bool;
ch0conf_mode_done: bool;
ch0conf_speed_done: bool |>`

(* SPI transmit *)
val _ = Datatype `tx_general_state =
| tx_idle | tx_enable_channel | tx_set_mode | tx_read_val_req
| tx_reply | tx_done | tx_disable_channel | tx_force`

val _ = Datatype `tx_state = <|
state: tx_general_state;
tx_buffer: word8 list;
tx_length: num;
tx_left_length: num;
interrupt: bool |>`

(* SPI receive *)
val _ = Datatype `rx_general_state =
| rx_idle | rx_enable_channel | rx_set_mode | rx_write_val_req
| rx_disable_channel | rx_reply | rx_done | rx_force`

val _ = Datatype `rx_state = <|
state: rx_general_state;
rx_buffer: word8 list;
rx_length: num;
rx_left_length: num;
interrupt: bool |>`

(* SPI registers, only related registers and bits are included. *)
(* Bits in SYSCONFIG register *)
val _ = Datatype `sysconfig_bits = <|
SIDLEMODE: word3; (* Power management *)
SOFTRESET: word1; (* Software reset *)
AUTOIDLE: word1 (* Internal OCP clock gating strategy *) |>`

(* Bits in MODULCTRL register *)
val _ = Datatype `modulctrl_bits = <|
SYSTEM_TEST: word1; (* enable the system test mode *)
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
DMAW: word1; (* DMA write request *)
DMAR: word1; (* DMA read request *)
DPE0: word1; (* Transmission enable for data line 0 *)
DPE1: word1; (* Transmission enable for data line 1 *)
IS: word1; (* Input select *)
TURBO: word1; (* Turbo mode *)
FORCE: word1 (* Manual SPIEN assertion to keep SPIEN active between SPI words *) |>`

(* Bits in CH0STAT register *)
val _ = Datatype `ch0stat_bits = <|
RXS: word1; (* Channel 0 receiver register status *)
TXS: word1; (* Channel 0 transmitter register status *)
EOT: word1 (* Channel 0 end-of-transfer status *) |>`

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
rx: rx_state (* receive state *) |>`

val _ = Datatype `mem_req = <|
pa: word32;
v: word8 option |>`

val _ = export_theory();
