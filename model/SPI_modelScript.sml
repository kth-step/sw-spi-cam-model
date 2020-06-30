open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_schedulerTheory SPI_txTheory write_SPIregsTheory read_SPIregsTheory;
open pred_setTheory wordsLib board_memTheory;


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
 * This function shows the SPI operation when it got a byte from memory in the tx/xfer processes.
 * Use bit TRM in CH0CONF to identify the tx and xfer processes.
*)
val spi_transition_mem_reply_def = Define `
spi_transition_mem_reply (spi:spi_state) (req:mem_req) =
if spi.regs.CH0CONF.TRM = 2w then tx_mem_reply_op spi req
else xfer_mem_reply_op spi req`

(* Some simple lemmas *)
(* If SPI bus is not initialized, the tx process can not start *)
val TX_FAIL_IF_NOT_INIT = store_thm("TX_FAIL_IF_NOT_INIT",
``!spi. (spi.init.state <> init_done) ==>
(spi_transition_write_regs SPI0_CH0CONF (0x00102000w:word32) spi).err``,
REPEAT STRIP_TAC >>
RW_TAC (std_ss++WORD_ss++SET_SPEC_ss) 
[spi_transition_write_regs_def,write_SPI_regs_def,SPI0_PA_RANGE_def,SPI0_CH0CONF_def,SPI0_MODULCTRL_def,SPI0_START_def,SPI0_END_def,write_CH0CONF_tx_def] >>
Cases_on `spi.tx.state` >>
RW_TAC std_ss []);

(* If SPI bus is not initialized, the rx process can not start *)
val RX_FAIL_IF_NOT_INIT = store_thm("RX_FAIL_IF_NOT_INIT",
``!spi. (spi.init.state <> init_done) ==>
(spi_transition_write_regs SPI0_CH0CONF (0x00101000w:word32) spi).err``,
REPEAT STRIP_TAC >>
RW_TAC (std_ss++WORD_ss++SET_SPEC_ss) 
[spi_transition_write_regs_def,write_SPI_regs_def,SPI0_PA_RANGE_def,SPI0_CH0CONF_def,SPI0_MODULCTRL_def,SPI0_START_def,SPI0_END_def,write_CH0CONF_rx_def] >>
Cases_on `spi.rx.state` >>
RW_TAC std_ss []);

val _ = export_theory();
