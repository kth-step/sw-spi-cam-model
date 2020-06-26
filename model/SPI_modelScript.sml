open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_schedulerTheory SPI_txTheory write_SPIregsTheory read_SPIregsTheory;

val _ = new_theory "SPI_model";

(* spi_transition_write_regs: word32 -> word32 -> spi_state -> spi_state 
   This function provides an interface that SPI handles the write request from the CPU when pa IN SPI_RAM *)
val spi_transition_write_regs_def = Define `
spi_transition_write_regs (pa:word32) (value:word32) (spi:spi_state) = 
write_SPI_regs pa value spi`

(* spi_transition_read_regs: environment -> word32 -> spi_state -> spi_state * word32 
   This function provides an interface that SPI return a value when CPU issue a read command *)
val spi_transition_read_regs_def = Define `
spi_transition_read_regs (env:environment) (pa:word32) (spi:spi_state) =
read_SPI_regs env pa spi`

(* spi_transition_autonomous: environment -> spi_state -> spi_state * mem_req
   This function indiciates SPI performed operations without any interaction with CPU or MEM *)
val spi_transition_autonomous_def = Define `
spi_transition_autonomous (env:environment) (spi:spi_state) =
scheduler spi env`

(* spi_transition_mem_reply: spi_state -> mem_req -> spi_state 
 * This function shows the SPI operation when it got a byte from memory in the tx process.
 * Since only in tx, SPI issues a memory request to get the value for sending out.
*)
val spi_transition_mem_reply_def = Define `
spi_transition_mem_reply (spi:spi_state) (req:mem_req) =
tx_mem_reply_op spi req`

val _ = export_theory();
