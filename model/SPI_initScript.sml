open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory;

val _ = new_theory "SPI_init";

(* In the SPI init state, the operation of reset. *)
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with
<| regs := spi.regs with 
   <| SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
      SYSSTATUS := 1w (* means reset is done *)|>;
   init := spi.init with state := init_setregs (* after reset is done, set up SPI registers *) |>`

(* This function shows initialization operations of SPI bus *)
val init_operations_def = Define `
init_operations (spi:spi_state) =
if spi.init.state = init_reset then
init_reset_op spi
else spi with err := T`
 

val _ = export_theory();
