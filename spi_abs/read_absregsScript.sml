open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open spi_absstateTheory;
open SPI_stateTheory board_memTheory read_SPIregsTheory;

val _ = new_theory "read_absregs"

(* read_abs_RX0: envvironment -> spi_abs_state -> spi_abs_state * word32 *)
val read_abs_RX0_def = Define `
read_abs_RX0 (env:environment) (spi_abs:spi_abs_state) =
let wl = (w2n spi_abs.regs.CH0CONF.WL) in
if (spi_abs.regs.CH0STAT.RXS = 1w) /\ (spi_abs.regs.CH0CONF.WL >+ 2w)
/\ (spi_abs.rx.state = abs_rx_data_ready) then 
(spi_abs with <|regs := spi_abs.regs with 
CH0STAT := spi_abs.regs.CH0STAT with RXS := 0w;
rx := spi_abs.rx with state := abs_rx_receive_data |>,
(wl >< 0) spi_abs.regs.RX0:word32)
else if  (spi_abs.regs.CH0STAT.RXS = 1w) /\ (spi_abs.regs.CH0CONF.WL >+ 2w)
/\ (spi_abs.xfer.state = abs_xfer_data_ready) /\ (spi_abs.regs.CH0STAT.TXS = 1w)
/\ (spi_abs.regs.CH0STAT.EOT = 1w) then
(spi_abs with <|regs := spi_abs.regs with
CH0STAT := spi_abs.regs.CH0STAT with RXS := 0w;
xfer := spi_abs.xfer with state := abs_xfer_ready_for_trans |>,
(wl >< 0) spi_abs.regs.RX0:word32)
else (spi_abs with err := T, env.read_reg)`

(* read_abs_spi_regs: environment -> word32 -> word32 -> spi_abs_state -> spi_abs_state * word32 *)
val read_abs_spi_regs = Define `
read_abs_spi_regs (env:environment) (pa:word32) (spi_abs:spi_abs_state) =
if spi_abs.err then (spi_abs, env.read_reg)
else if ~(pa IN SPI0_PA_RANGE) then (spi_abs, env.read_reg)
else if pa = SPI0_SYSCONFIG then (spi_abs, build_SYSCONFIG spi_abs.regs.SYSCONFIG)
else if pa = SPI0_SYSSTATUS then (spi_abs, w2w spi_abs.regs.SYSSTATUS)
else if pa = SPI0_MODULCTRL then (spi_abs, build_MODULCTRL spi_abs.regs.MODULCTRL)
else if pa = SPI0_CH0CONF then (spi_abs, build_CH0CONF spi_abs.regs.CH0CONF)
else if pa = SPI0_CH0STAT then (spi_abs, build_CH0STAT spi_abs.regs.CH0STAT)
else if pa = SPI0_CH0CTRL then (spi_abs, w2w spi_abs.regs.CH0CTRL)
else if pa = SPI0_TX0 then (spi_abs, spi_abs.regs.TX0)
else if pa = SPI0_RX0 then (read_abs_RX0 env spi_abs)
else (spi_abs, env.read_reg)`

val _ = export_theory();
