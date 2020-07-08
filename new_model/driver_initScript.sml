open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory write_SPIregsTheory read_SPIregsTheory board_memTheory;

val _ = new_theory "driver_init";

(* SPI controller performs operation of reset. *)
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with regs := spi.regs with 
   <| SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
      SYSSTATUS := 1w (* means reset is done *)|>`

(* This function shows initialization operations of SPI driver considering SPI controller state *)
val init_operations_def = Define `
init_operations (env:environment) (spi:spi_state) (driver:spi_driver) =
let (read_spi,sysstatus) = (read_SPI_regs env SPI0_SYSSTATUS spi driver) in
case driver.init.state of
  | init_start => (write_SPI_regs SPI0_SYSCONFIG (2w:word32) spi driver)
  | init_reset => if sysstatus = (1w:word32) then (read_spi,driver with init := driver.init with state := init_setregs)
                  else (init_reset_op spi, driver)
  | init_setregs => if ~driver.init.sysconfig_mode_done  then 
                    (write_SPI_regs SPI0_SYSCONFIG (0x11w:word32) spi driver)
    else if ~driver.init.modulctrl_bus_done then
    (write_SPI_regs SPI0_MODULCTRL (1w:word32) spi driver)
    else if ~driver.init.ch0conf_wordlen_done then
    (write_SPI_regs SPI0_CH0CONF (0x700w:word32) spi driver)
    else if ~driver.init.ch0conf_mode_done then
    (write_SPI_regs SPI0_CH0CONF (0x00010040w:word32) spi driver)
    else if ~driver.init.ch0conf_speed_done then
    (write_SPI_regs SPI0_CH0CONF (0x18w:word32) spi driver)
    else (spi, driver with init := driver.init with state := init_done)
  | init_done => (spi, driver)`

val _ = export_theory();
