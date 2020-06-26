open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open board_memTheory SPI_stateTheory;

val _ = new_theory "read_SPIregs";

(* concat sysconfig bits into a 32-bits word *)
val build_SYSCONFIG_def = Define `
build_SYSCONFIG (SYSCONFIG:sysconfig_bits) =
let v1 = (0w:word1 @@ (SYSCONFIG.SOFTRESET @@ 
SYSCONFIG.AUTOIDLE) :word2): word3 in
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

(* read_register returns a new spi state and the value of pa *)
val read_SPI_regs_def = Define `
read_SPI_regs (env:environment) (pa:word32) (spi:spi_state) =
if spi.err  then (spi, env.read_reg)
else if ~(pa IN SPI0_PA_RANGE) then (spi with err := T, env.read_reg) 
else if pa = SPI0_SYSCONFIG then (spi, build_SYSCONFIG spi.regs.SYSCONFIG)
else if pa = SPI0_SYSSTATUS then (spi, w2w spi.regs.SYSSTATUS)
else if pa = SPI0_MODULCTRL then (spi, build_MODULCTRL spi.regs.MODULCTRL)
else if pa = SPI0_CH0CONF then (spi, build_CH0CONF spi.regs.CH0CONF)
else if pa = SPI0_CH0STAT then (spi, build_CH0STAT spi.regs.CH0STAT)
else if pa = SPI0_CH0CTRL then (spi, w2w spi.regs.CH0CTRL)
else if pa = SPI0_TX0 then (spi, w2w spi.regs.TX0)
else if pa = SPI0_RX0 then (spi, w2w spi.regs.RX0)
else (spi, env.read_reg)`

val _ = export_theory();
