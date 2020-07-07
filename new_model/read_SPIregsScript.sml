open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open board_memTheory SPI_stateTheory;

val _ = new_theory "read_SPIregs";

(* concat sysconfig bits into a 32-bits word *)
val build_SYSCONFIG_def = Define `
build_SYSCONFIG (SYSCONFIG:sysconfig_bits) =
(* during read, bit SOFRRESET always returns 0 *)
let v1 = (0w:word2 @@ SYSCONFIG.AUTOIDLE): word3 in
(SYSCONFIG.SIDLEMODE @@ v1) :word32`

(* concat modulctrl bits into a 32-bits word *)
val build_MODULCTRL_def = Define `
build_MODULCTRL (MODULCTRL:modulctrl_bits) =
(MODULCTRL.MS @@ ((0w:word1 @@ MODULCTRL.SINGLE):word2)):word32`

(* concat ch0conf bits into a 32-bits word*)
val build_CH0CONF_def = Define `
build_CH0CONF (CH0CONF:ch0conf_bits) = 
let v1 = (CH0CONF.FORCE @@ ((CH0CONF.TURBO @@ ((CH0CONF.IS @@ 
((CH0CONF.DPE1 @@ CH0CONF.DPE0):word2)):word3)):word4)):word5 and
v2 = ((((0w:word2 @@ CH0CONF.TRM):word4) @@
((CH0CONF.WL @@
((CH0CONF.EPOL @@
((CH0CONF.CLKD @@ 
((CH0CONF.POL @@ CH0CONF.PHA)
:word2)):word6)):word7)):word12)):word16) in
(v1 @@ v2):word32`

(* concat ch0stat bits into a 32-bits word *)
val build_CH0STAT_def = Define `
build_CH0STAT (CH0STAT:ch0stat_bits) =
(CH0STAT.EOT @@ ((CH0STAT.TXS @@ CH0STAT.RXS):word2)):word32`

(* Test to concat words
EVAL ``(1w:word1 @@ (1w:word1 @@ (1w:word1 @@ 3w:word2):word3):word4):word32`` 
 *)

(* read the value of RX0 with certain word-length*)
val read_RX0_def = Define `
read_RX0 (spi:spi_state) =
let wl = (w2n spi.regs.CH0CONF.WL) + 1 in
(wl >< 0) spi.regs.RX0:word32`

(* read_register returns a new spi state and the value of pa *)
val read_SPI_regs_def = Define `
read_SPI_regs (env:environment) (pa:word32) 
(spi:spi_state) (driver:spi_driver) =
if spi.err  then (spi, env.read_reg)
else if ~(pa IN SPI0_PA_RANGE) then (spi with err := T, env.read_reg)
(* most regs can be read at any time *)
else if pa = SPI0_SYSCONFIG then (spi, build_SYSCONFIG spi.regs.SYSCONFIG)
else if pa = SPI0_SYSSTATUS then (spi, w2w spi.regs.SYSSTATUS)
else if pa = SPI0_MODULCTRL then (spi, build_MODULCTRL spi.regs.MODULCTRL)
else if pa = SPI0_CH0CONF then (spi, build_CH0CONF spi.regs.CH0CONF)
else if pa = SPI0_CH0STAT then (spi, build_CH0STAT spi.regs.CH0STAT)
else if pa = SPI0_CH0CTRL then (spi, w2w spi.regs.CH0CTRL)
else if pa = SPI0_TX0 then (spi, spi.regs.TX0)
(* a read for RX0 is vaild when RXS = 1 *)
else if pa = SPI0_RX0 /\ (CHECK_RXS_BIT spi) /\ (spi.regs.CH0CONF.WL >+ 3w) 
then (spi, read_RX0 spi)
else if pa = SPI0_RX0 /\ (~(CHECK_RXS_BIT spi) \/ (spi.regs.CH0CONF.WL <=+ 3w))
then (spi with err := T, env.read_reg)
(* other addresses in SPI are not modeled, return an arbitrary value *)
else (spi, env.read_reg)`

val _ = export_theory();