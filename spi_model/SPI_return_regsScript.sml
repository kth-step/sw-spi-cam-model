open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open board_memTheory SPI_stateTheory;

val _ = new_theory "SPI_return_regs";

(* build_SYSCONFIG: connect sysconfig bits into a 32-bits word. *)
val build_SYSCONFIG_def = Define `
build_SYSCONFIG (SYSCONFIG:sysconfig_bits) =
(* During reads bit SOFRRESET always returns 0 *)
let v1 = (0w:word2 @@ SYSCONFIG.AUTOIDLE): word3 in
(SYSCONFIG.SIDLEMODE @@ v1) :word32`

(* build_MODULCTRL: connect modulctrl bits into a 32-bits word. *)
val build_MODULCTRL_def = Define `
build_MODULCTRL (MODULCTRL:modulctrl_bits) =
(MODULCTRL.MS @@ ((0w:word1 @@ MODULCTRL.SINGLE):word2)) :word32`

(* build_CH0CONF: connect ch0conf bits into a 32-bits word. *)
val build_CH0CONF_def = Define `
build_CH0CONF (CH0CONF:ch0conf_bits) = 
let v1 = (CH0CONF.FORCE @@ ((0w:word1 @@ ((CH0CONF.IS @@ 
((CH0CONF.DPE1 @@ CH0CONF.DPE0):word2)):word3)):word4)):word5 and
v2 = ((((0w:word2 @@ CH0CONF.TRM):word4) @@
((CH0CONF.WL @@
((CH0CONF.EPOL @@
((CH0CONF.CLKD @@ 
((CH0CONF.POL @@ CH0CONF.PHA)
:word2)):word6)):word7)):word12)):word16) in
(v1 @@ v2) :word32`

(* build_CH0STAT: connect ch0stat bits into a 32-bits word. *)
val build_CH0STAT_def = Define `
build_CH0STAT (CH0STAT:ch0stat_bits) =
(CH0STAT.EOT @@ ((CH0STAT.TXS @@ CH0STAT.RXS):word2)):word32`

(* read_RX0: fetch the data in the RX0 register. *)
val read_RX0_def = Define `
read_RX0 (spi:spi_state) =
if (CHECK_RXS_BIT spi) /\ (spi.state = rx_data_ready) then
(spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT with RXS := 0w;
state := rx_receive_data |>,
(7 >< 0) spi.regs.RX0:word32)
else if (CHECK_RXS_BIT spi) /\ (spi.state = xfer_data_ready) then
(spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT with RXS := 0w;
state := xfer_ready_for_trans |>,
(7 >< 0) spi.regs.RX0:word32)
else (spi with err := T, ARB)`

(* read_SPI_regs: returns a new spi state and the value of the memory-mapped register. *)
val read_SPI_regs_def = Define `
read_SPI_regs (pa:word32) (spi:spi_state) =
(* pa is not in the SPI region, no changes *)
if ~(pa IN SPI0_PA_RANGE) then (spi, ARB)
(* most regs can be read at any time *)
else if pa = SPI0_SYSCONFIG then (spi, build_SYSCONFIG spi.regs.SYSCONFIG)
else if pa = SPI0_SYSSTATUS then (spi, w2w spi.regs.SYSSTATUS)
else if pa = SPI0_MODULCTRL then (spi, build_MODULCTRL spi.regs.MODULCTRL)
else if pa = SPI0_CH0CONF then (spi, build_CH0CONF spi.regs.CH0CONF)
else if pa = SPI0_CH0STAT then (spi, build_CH0STAT spi.regs.CH0STAT)
else if pa = SPI0_CH0CTRL then (spi, w2w spi.regs.CH0CTRL)
else if pa = SPI0_TX0 then (spi, spi.regs.TX0)
(* a read for RX0 is vaild when RXS = 1 *)
else if pa = SPI0_RX0 then (read_RX0 spi)
(* other addresses in SPI are not modeled, return an arbitrary value *)
else (spi, ARB)`

(* read_SPI_regs_state, read_SPI_regs_value: return specific datatypes *)
val read_SPI_regs_state_def = Define `
read_SPI_regs_state (pa:word32) (spi:spi_state) =
let (spi', v) = read_SPI_regs pa spi in spi'`

val read_SPI_regs_value_def = Define `
read_SPI_regs_value (pa:word32) (spi:spi_state) =
let (spi', v) = read_SPI_regs pa spi in v`

val _ = export_theory();
