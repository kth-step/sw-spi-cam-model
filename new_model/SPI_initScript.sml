open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_init";

(* SPI controller performs reset operation.
 * init_reset_op: spi_state -> spi_state
 *)
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with <| regs := spi.regs with 
   <| SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
      SYSSTATUS := 1w (* means reset is done *)|>;
   init := spi.init with state := init_setregs (* enter to next init step *) |>`

(* This function shows initialization operations of SPI controller, spi -> spi'.
 * spi_init_operations: spi_state -> spi_state
 *)
val spi_init_operations_def = Define `
spi_init_operations (spi:spi_state) =
case spi.init.state of
  | init_start => spi with err := T
  | init_reset => init_reset_op spi
  | init_setregs => spi with err := T
  | init_done => spi with err := T`

val _ = export_theory()
