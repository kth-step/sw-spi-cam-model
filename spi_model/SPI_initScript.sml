open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_init";

(* SPI controller performs reset operation.
 * init_reset_op: spi_state -> spi_state
 *)
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with <| regs := spi.regs with SYSSTATUS := 1w (* indiciate reset is done *);
init := spi.init with state := init_setregs (* enter the next init state, set up SPI registers *) |>`

(* Another version: Reset every register to its default value 
val init_reset_op_def = Define `
init_reset_op (spi:spi_state) = 
spi with <|regs := spi.regs with
   <| SYSCONFIG := spi.regs.SYSCONFIG with <| SIDLEMODE := 0w; SOFTRESET := 0w; AUTOIDLE := 0w|>;
      SYSSCONFIG := 1w;
      MODULCTRL := spi.regs.MODULCTRL with <| SYSTEM_TEST := 0w; MS := 1w; SINGLE := 0w |>;
      CH0CONF := spi.regs.CH0CONF with <| PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w;
      WL := 0w; TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; TURBO := 0W; FORCE := 0w |>;
      CH0STAT := spi.regs.CH0STAT <| RXS := 0w; TXS := 0w; EOT := 0w |>;
      CH0CTRL := 0w;
      TX0 := 0w;
      RX0 := 0w |>;
      init := spi.init with state := init_setregs |>`
 *) 

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

(* INIT_SYN_ENABLE/DISABLE: spi.init.state -> bool *)
val INIT_SYN_ENABLE_def = Define `
INIT_SYN_ENABLE (init_s:init_general_state) =
(init_s = init_done)`

val INIT_SYN_DISABLE_def = Define `
INIT_SYN_DISABLE (init_s:init_general_state) =
(init_s = init_start)`

val _ = export_theory();
