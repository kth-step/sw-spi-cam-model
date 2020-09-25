open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open spi_refstateTheory;
open SPI_stateTheory board_memTheory read_SPIregsTheory;

val _ = new_theory "read_refregs"

(* read_ref_RX0: envvironment -> spi_ref_state -> spi_ref_state * word32 *)
val read_ref_RX0_def = Define `
read_ref_RX0 (env:environment) (spi_ref:spi_ref_state) =
let wl = (w2n spi_ref.regs.CH0CONF.WL) in
if (spi_ref.regs.CH0STAT.RXS = 1w) /\ (spi_ref.regs.CH0CONF.WL >+ 2w)
/\ (spi_ref.rx.state = ref_rx_data_ready) then 
(spi_ref with <|regs := spi_ref.regs with 
CH0STAT := spi_ref.regs.CH0STAT with RXS := 0w;
rx := spi_ref.rx with state := ref_rx_receive_data |>,
(wl >< 0) spi_ref.regs.RX0:word32)
else if  (spi_ref.regs.CH0STAT.RXS = 1w) /\ (spi_ref.regs.CH0CONF.WL >+ 2w)
/\ (spi_ref.xfer.state = ref_xfer_data_ready) /\ (spi_ref.regs.CH0STAT.TXS = 1w)
/\ (spi_ref.regs.CH0STAT.EOT = 1w) then
(spi_ref with <|regs := spi_ref.regs with
CH0STAT := spi_ref.regs.CH0STAT with RXS := 0w;
xfer := spi_ref.xfer with state := ref_xfer_ready_for_trans |>,
(wl >< 0) spi_ref.regs.RX0:word32)
else (spi_ref with err := T, env.read_reg)`

(* read_ref_spi_regs: environment -> word32 -> word32 -> spi_ref_state -> spi_ref_state * word32 *)
val read_ref_spi_regs = Define `
read_ref_spi_regs (env:environment) (pa:word32) (spi_ref:spi_ref_state) =
if spi_ref.err then (spi_ref, env.read_reg)
else if ~(pa IN SPI0_PA_RANGE) then (spi_ref, env.read_reg)
else if pa = SPI0_SYSCONFIG then (spi_ref, build_SYSCONFIG spi_ref.regs.SYSCONFIG)
else if pa = SPI0_SYSSTATUS then (spi_ref, w2w spi_ref.regs.SYSSTATUS)
else if pa = SPI0_MODULCTRL then (spi_ref, build_MODULCTRL spi_ref.regs.MODULCTRL)
else if pa = SPI0_CH0CONF then (spi_ref, build_CH0CONF spi_ref.regs.CH0CONF)
else if pa = SPI0_CH0STAT then (spi_ref, build_CH0STAT spi_ref.regs.CH0STAT)
else if pa = SPI0_CH0CTRL then (spi_ref, w2w spi_ref.regs.CH0CTRL)
else if pa = SPI0_TX0 then (spi_ref, spi_ref.regs.TX0)
else if pa = SPI0_RX0 then (read_ref_RX0 env spi_ref)
else (spi_ref, env.read_reg)`

val _ = export_theory();
