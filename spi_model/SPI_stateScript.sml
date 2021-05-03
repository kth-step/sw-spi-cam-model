open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open board_memTheory;

val _ = new_theory "SPI_state";

(* spi_state: the SPI controller's state that contains registers, an error flag and automaton's states *)

(* SPI registers: memory-mapped SPI registers, only related registers and bits are included. *)
(* Bits in the SYSCONFIG register *)
val _ = Datatype `sysconfig_bits = <|
SIDLEMODE: word2; (* Smart-idle mode *)
SOFTRESET: word1; (* Software reset *)
AUTOIDLE: word1 (* Internal OCP clock gating strategy *) |>`

(* Bits in the MODULCTRL register *)
val _ = Datatype `modulctrl_bits = <|
SYSTEM_TEST: word1; (* Enable system test mode *)
MS: word1; (* Master/Slave *)
SINGLE: word1 (* Single/multi channels, master mode only *)|>`

(* Bits in the CH0CONF register *)
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
FORCE: word1 (* Manual SPIEN assertion to keep SPIEN active between SPI words *) |>`

(* Bits in the CH0STAT register *)
val _ = Datatype `ch0stat_bits = <|
RXS: word1; (* Channel 0 receiver register status *)
TXS: word1; (* Channel 0 transmitter register status *)
EOT: word1  (* Channel 0 end-of-transfer status *) |>`

(* SPI memory-mapped registers *)
val _ = Datatype `spi_regs = <|
SYSCONFIG: sysconfig_bits; (* system configuration register *)
SYSSTATUS: word1; (* system status register, only RESETDONE bit *)
MODULCTRL: modulctrl_bits; (* module control register *)
CH0CONF: ch0conf_bits; (* channel 0 configuration register *)
CH0STAT: ch0stat_bits; (* channel 0 status register *)
CH0CTRL: word1; (* channel 0 control register *)
TX0: word32; (* channel 0 transmit buffer register *)
RX0: word32 (*channel 0 receive buffer register *)|>`

(* spi general state *)
val _ = Datatype `spi_general_state = 
| init_start | init_reset | init_setregs | spi_ready 
| tx_conf_ready | tx_channel_enabled | tx_ready_for_trans
| tx_trans_data | tx_trans_done | tx_trans_next 
| tx_trans_update | tx_channel_disabled
| rx_conf_ready | rx_channel_enabled | rx_receive_data 
| rx_update_RX0 | rx_data_ready | rx_channel_disabled
| xfer_conf_ready | xfer_channel_enabled | xfer_ready_for_trans 
| xfer_trans_data | xfer_exchange_data | xfer_update_RX0 
| xfer_data_ready | xfer_channel_disabled`

(* boolean flags to record the init process *)
val _ = Datatype `init_flags = <|
sysconfig_mode_done: bool;
modulctrl_bus_done: bool |>`

(* spi_state: spi controller state *)
val _ = Datatype `spi_state = <|
err: bool; (* an error flag for SPI state*)
state : spi_general_state; (* SPI general state*)
regs: spi_regs; (* SPI registers *)
TX_SHIFT_REG : word8; (* Shift register to transmit data, not memory-mapped SPI register *)
RX_SHIFT_REG : word8; (* Shift register to receive data, not memory-mapped SPI register *)
init: init_flags; (* initialization flags *) |>`

(* Some simple functions related to the spi_state *)
(* CHECK_RXS_BIT: check SPI register CH0STAT RXS Bit. *)
val CHECK_RXS_BIT_def = Define `
CHECK_RXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.RXS = 1w)`

(* CHECK_TXS_BIT: check SPI register CH0STAT TXS Bit. *)
val CHECK_TXS_BIT_def = Define `
CHECK_TXS_BIT (spi:spi_state) = (spi.regs.CH0STAT.TXS = 1w)`

(* CHECK_EOT_BIT: check SPI register CH0STAT EOT Bit. *)
val CHECK_EOT_BIT_def = Define `
CHECK_EOT_BIT (spi:spi_state) = (spi.regs.CH0STAT.EOT = 1w)`

(* Externel environment connected to the SPI bus 
val _ = Datatype `environment = <|
read_reg : word32 (* An arbitrary value *)|>`
*)

(* global_lbl_type: describe the labeled state transitions. *)
(* tau means internal transition, TX, RX and XFER: SPI devices transmit and receive data, 
 * Write and Read are CPU/driver-issued commands to SPI memory-mapped registers.
 * Update and Return are SPI opertations according to CPU Write and Read commands, respectively.
 * call_... : driver's interface for other programs to call its specific functions.
 *)
val _ = Datatype `global_lbl_type = 
| tau | TX (word8 option) | RX (word8 option) | XFER (word8 option) (word8 option)
| Write word32 word32 | Update word32 word32 | Read word32 word32 | Return word32 word32
| call_init | call_tx (word8 list) | call_rx num | call_xfer (word8 list) | call_back (word8 list)`

val _ = export_theory();
