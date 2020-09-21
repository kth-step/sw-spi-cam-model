open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory SPI_schedulerTheory; 
open write_SPIregsTheory read_SPIregsTheory;
open SPI_initTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;

val _ = new_theory "SPI_relation";

(* tr: (state) transition *)
(* Some functions return specific datatypes *)
val read_SPI_regs_state_def = Define `
read_SPI_regs_state (env:environment) (pa:word32) (spi:spi_state) =
let (spi', v) = read_SPI_regs env pa spi in spi'`

val read_SPI_regs_value_def = Define `
read_SPI_regs_value (env:environment) (pa:word32) (spi:spi_state) =
let (spi', v) = read_SPI_regs env pa spi in v`

val tx_trans_done_op_state_def = Define `
tx_trans_done_op_state (spi:spi_state) =
let (spi', v_option) = tx_trans_done_op spi in spi'`

val tx_trans_done_op_value_def = Define `
tx_trans_done_op_value (spi:spi_state) =
let (spi', v_option) = tx_trans_done_op spi in v_option`

val xfer_exchange_data_op_state_def = Define `
xfer_exchange_data_op_state (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in spi'`

val xfer_exchange_data_op_value_def = Define `
xfer_exchange_data_op_value (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in v_option`

(* relation for spi transition (an SPI device). *)
val (spi_tr_rules, spi_tr_ind, spi_tr_cases) = Hol_reln `
(!(spi:spi_state). T ==> spi_tr spi (Update a v) (write_SPI_regs a v spi)) /\
(!(spi:spi_state). T ==> spi_tr spi (Return a (read_SPI_regs_value env a spi)) (read_SPI_regs_state env a spi)) /\
(!(spi:spi_state). (env.scheduler = Initialize) /\ (INIT_ENABLE spi) ==>
spi_tr spi tau (spi_init_operations spi)) /\
(!(spi:spi_state). (env.scheduler = Transmit) /\ (TX_ENABLE spi) ==>
spi_tr spi tau (spi_tx_operations spi)) /\
(!(spi:spi_state). (env.scheduler = Receive) /\ (RX_ENABLE spi) ==>
spi_tr spi tau (spi_rx_operations spi)) /\
(!(spi:spi_state). (env.scheduler = Transfer) /\ (XFER_ENABLE spi) ==>
spi_tr spi tau (spi_xfer_operations spi)) /\
(!(spi:spi_state). (spi.tx.state = tx_trans_done) ==> 
spi_tr spi (TX (tx_trans_done_op_value spi)) (tx_trans_done_op_state spi)) /\
(!(spi:spi_state). (spi.rx.state = rx_receive_data) ==> 
spi_tr spi (RX data) (rx_receive_data_op spi data)) /\
(!(spi:spi_state). (spi.xfer.state = xfer_exchange_data) ==>
spi_tr spi (XFER dataIN (xfer_exchange_data_op_value spi dataIN)) (xfer_exchange_data_op_state spi dataIN))`

(*
(* relation for local transition (an SPI device and a CPU)
 * CPU's datatype could be arm_state or the driver's datatype we defined later.
 *)
val (local_tr_rules, local_tr_ind, local_tr_cases) = Hol_reln `
(!(cpu:'a) (spi:spi_state).
cpu_tr cpu tau cpu' ==> local_tr (cpu, spi) tau (cpu', spi)) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi tau spi' ==> local_tr (cpu, spi) tau (cpu, spi')) /\
(!(cpu:'a) (spi:spi_state).
(cpu_tr cpu (Write a v) cpu') /\
(spi_tr spi (Update a v) spi') ==>
local_tr (cpu, spi) tau (cpu', spi')) /\
(!(cpu:'a) (spi:spi_state).
(cpu_tr cpu (Read a v) cpu') /\
(spi_tr spi (Return a v) spi') ==>
local_tr (cpu, spi) tau (cpu', spi')) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi (TX data) spi' ==> local_tr (cpu, spi) (TX data) (cpu, spi')) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi (RX data) spi' ==> local_tr (cpu, spi) (RX data) (cpu, spi')) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi (XFER dataIN dataOUT) spi' ==> local_tr (cpu, spi) (XFER dataIN dataOUT) (cpu, spi'))`

(* relation for global transition (two SPI devices and two CPUs) *)
val (gloabl_tr_rules, global_tr_ind, global_tr_cases) = Hol_reln `
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
local_tr (cpu1, spi1) tau (cpu1', spi1') ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2, spi2)) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
local_tr (cpu2, spi2) tau (cpu2', spi2') ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1, spi1, cpu2', spi2')) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
(local_tr (cpu1, spi1) (TX data) (cpu1, spi1')) /\
(local_tr (cpu2, spi2) (RX data) (cpu2, spi2')) ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2', spi2')) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
(local_tr (cpu1, spi1) (RX data) (cpu1', spi1')) /\
(local_tr (cpu2, spi2) (TX data) (cpu2', spi2')) ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2', spi2')) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state).
(local_tr (cpu1, spi1) (XFER data1 data2) (cpu1', spi1')) /\
(local_tr (cpu2, spi2) (XFER data2 data1) (cpu2', spi2')) ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2', spi2'))`
*)

val _ = export_theory();
