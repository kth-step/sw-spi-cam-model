open HolKernel bossLib boolLib Parse wordsTheory wordsLib;

(* This script defines the memory space on the board for AM335x CPU. *)
val _ = new_theory "board_mem";

(* Physical start address of RAM on board *)
val BOARD_RAM_START_def = Define `BOARD_RAM_START = 0x80000000w:word32`

(* Physical ending address (exclusive) of RAM on board *)
val BOARD_RAM_END_def = Define `BOARD_RAM_END = 0xA0000000w:word32`

(* Physical start addresses of SPI0 memory-mapped registers on board *)
val SPI0_START_def = Define `SPI0_START = 0x48030000w:word32`

(* Physical end address (exclusive) of SPI0 memory-mapped registers on board *)
val SPI0_END_def = Define `SPI0_END = 0x48031000w:word32`

(* Physical address range of SPI0 *)
val SPI0_PA_RANGE_def = Define `SPI0_PA_RANGE = {x| SPI0_START <=+ x /\ x <+ SPI0_END}`

(* Physical addresses of SPI0 memory-mapped registers that are used in the model *)
(* SPI0_SYSCONFIG: system configuration register *)
val SPI0_SYSCONFIG_def = Define `SPI0_SYSCONFIG = 0x48030110w:word32`

(* SPI0_SYSSTATUS: system status register *)
val SPI0_SYSSTATUS_def = Define `SPI0_SYSSTATUS = 0x48030114w:word32`

(* SPI0_MODULCTRL: module control register *)
val SPI0_MODULCTRL_def = Define `SPI0_MODULCTRL = 0x48030128w:word32`

(* SPI0_CH0CONF: channel 0 configuration register *)
val SPI0_CH0CONF_def = Define `SPI0_CH0CONF = 0x4803012Cw:word32`

(* SPI0_CH0STAT: channel 0 status register*)
val SPI0_CH0STAT_def = Define `SPI0_CH0STAT = 0x48030130w:word32`

(* SPI0_CH0CTRL: channel 0 control register *)
val SPI0_CH0CTRL_def = Define `SPI0_CH0CTRL = 0x48030134w:word32`

(* SPI0_TX0: channel 0 transmit buffer register *)
val SPI0_TX0_def = Define `SPI0_TX0 = 0x48030138w:word32`

(* SPI0_RX0: channel 0 receive buffer register *)
val SPI0_RX0_def = Define `SPI0_RX0 = 0x4803013Cw:word32`

val _ = export_theory();
