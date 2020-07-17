open HolKernel bossLib boolLib Parse;
open SPI_stateTheory write_SPIregsTheory read_SPIregsTheory SPI_schedulerTheory;

val _ = new_theory "SPI_model";

(* write and read interfaces for SPI controller and the driver/CPU through memory-mapped registers *)
(* This function provides an interface that SPI controller handles 
 * the write request from the CPU when pa IN SPI_RAM.
 * spi_transition_write_regs: word32 -> word32 -> spi_state -> spi_state  *)
val spi_transition_write_regs_def = Define `
spi_transition_write_regs (pa:word32) (value:word32) (spi:spi_state) = 
write_SPI_regs pa value spi`

(* This function provides an interface that SPI controller
 * returns a value when CPU issue a read request.
 * env is used to returen an arbitrary value.
 * spi_transition_read_regs: environment -> word32 -> spi_state -> spi_state * word32 
 *)
val spi_transition_read_regs_def = Define `
spi_transition_read_regs (env:environment) (pa:word32) (spi:spi_state) =
read_SPI_regs env pa spi`

(* SPI hardware internal operations without the interactions with CPU/driver *)
(* SPI internal operations with a scheduler. 
 * spi_transition_autonomous: environment -> spi_state -> spi_state
 *)
val spi_transition_autonomous_def = Define `
spi_transition_autonomous (env:environment) (spi:spi_state) =
spi_scheduler env spi`

val _ = export_theory();
