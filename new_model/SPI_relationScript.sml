open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory write_SPIregsTheory read_SPIregsTheory SPI_initTheory SPI_txTheory SPI_rxTheory;

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
tx_trans_done_op_state (spi:spi_state) (spi':spi_state) =
let (spi_new, v_option) = tx_trans_done_op spi spi' in spi_new`

val tx_trans_done_op_value_def = Define `
tx_trans_done_op_value (spi:spi_state) (spi':spi_state) =
let (spi_new, v_option) = tx_trans_done_op spi spi' in v_option`

(* relation for spi transition (an SPI device).
 * Here spi' is another spi device.
 *)
val (spi_tr_rules, spi_tr_ind, spi_tr_cases) = Hol_reln `
(!(spi:spi_state). T ==> spi_tr spi (Update a v) (write_SPI_regs a v spi)) /\
(!(spi:spi_state). T ==> spi_tr spi (Return a (read_SPI_regs_value env a spi)) (read_SPI_regs_state env a spi)) /\
(!(spi:spi_state). (env.scheduler = Initialize) /\ (INIT_ENABLE spi) ==>
spi_tr spi tau (spi_init_operations spi)) /\
(!(spi:spi_state). (env.scheduler = Transmit) /\ (TX_ENABLE spi) ==>
spi_tr spi tau (spi_tx_operations spi)) /\
(!(spi:spi_state). (env.scheduler = Receive) /\ (RX_ENABLE spi) ==>
spi_tr spi tau (spi_rx_operations spi)) /\
(!(spi:spi_state) (spi':spi_state). (spi.tx.state = tx_trans_done) ==> 
spi_tr spi (TX (tx_trans_done_op_value spi spi')) (tx_trans_done_op_state spi spi')) /\
(!(spi:spi_state) (spi':spi_state). (spi.rx.state = rx_receive_data) ==> 
spi_tr spi (RX data) (rx_receive_data_op spi spi' data))`

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
(cpu_tr cpu (Read a) cpu') /\
(spi_tr spi (Return a v) spi') ==>
local_tr (cpu, spi) tau (cpu', spi')) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi (TX data) spi' ==> local_tr (cpu, spi) (TX data) (cpu, spi')) /\
(!(cpu:'a) (spi:spi_state).
spi_tr spi (RX data) spi' ==> local_tr (cpu, spi) (RX data) (cpu, spi'))`

(* relation for global transition (two SPI devices and two CPUs) *)
val (gloabl_tr_rules, global_tr_ind, global_tr_cases) = Hol_reln `
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
local_tr (cpu1, spi1) tau (cpu1', spi1') ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2, spi2)) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
local_tr (cpu2, spi2) tau (cpu2', spi2') ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1, spi1, cpu2', spi2')) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
(local_tr (cpu1, spi1) (TX data) (cpu1', spi1')) /\
(local_tr (cpu2, spi2) (RX data) (cpu2', spi2')) ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2', spi2')) /\
(!(cpu1:'a) (spi1:spi_state) (cpu2:'a) (spi2:spi_state). 
(local_tr (cpu1, spi1) (RX data) (cpu1', spi1')) /\
(local_tr (cpu2, spi2) (TX data) (cpu2', spi2')) ==>
global_tr (cpu1, spi1, cpu2, spi2) (cpu1', spi1', cpu2', spi2'))`

val SPI_tx_data = store_thm("SPI_tx_data",
``!spi1 spi1' data spi2.
(spi1.tx.state = tx_trans_done) /\ (spi1' = tx_trans_done_op_state spi1 spi2) /\
(spi2.rx.state = rx_receive_data) /\ (spi2.regs.CH0STAT.RXS = 0w) /\
(data = tx_trans_done_op_value spi1 spi2) ==>
((spi_tr spi1 (TX data) spi1') /\
(data = SOME spi1.TX_SHIFT_REG))``,
REPEAT STRIP_TAC >>
RW_TAC std_ss [spi_tr_cases] >|
[EXISTS_TAC ``spi2:spi_state`` >>
METIS_TAC[],
RW_TAC std_ss [tx_trans_done_op_value_def,tx_trans_done_op_def]]);

val SPI_rx_data = store_thm("SPI_rx_data",
``!spi1 spi1' spi2 data. 
(data <> NONE) /\ (spi1.rx.state = rx_receive_data) /\ (spi1.regs.CH0STAT.RXS = 0w) /\
(spi1' = rx_receive_data_op spi1 spi2 data) /\ (spi2.tx.state = tx_trans_done) ==>
((spi_tr spi1 (RX data) spi1') /\ (spi1'.RX_SHIFT_REG = THE data))``,
REPEAT STRIP_TAC >>
RW_TAC std_ss [spi_tr_cases] >|
[EXISTS_TAC ``spi2:spi_state`` >>
METIS_TAC[],
RW_TAC std_ss [rx_receive_data_op_def]]);

val SPI_TX_and_RX_data = store_thm("SPI_TX_and_RX",
``!cpu1 cpu2 spi1 spi2.
(spi1.tx.state = tx_trans_done) /\ (spi2.rx.state = rx_receive_data) /\
(spi2.regs.CH0STAT.RXS = 0w) /\
(spi1' = tx_trans_done_op_state spi1 spi2) /\
(data = tx_trans_done_op_value spi1 spi2) /\
(spi2' = rx_receive_data_op spi2 spi1 data) ==>
(global_tr (cpu1, spi1, cpu2, spi2) (cpu1, spi1', cpu2, spi2')) /\
(spi2'.RX_SHIFT_REG = spi1.TX_SHIFT_REG)``,
REPEAT STRIP_TAC >|
[`spi_tr spi1 (TX data) spi1'` by METIS_TAC[SPI_tx_data] >>
`data = SOME spi1.TX_SHIFT_REG` by METIS_TAC[SPI_tx_data] >>
`data <> NONE` by RW_TAC (std_ss++WORD_ss) [] >>
`spi_tr spi2 (RX data) spi2'` by METIS_TAC[SPI_rx_data] >>
`local_tr (cpu1, spi1) (TX data) (cpu1, spi1')` by METIS_TAC[local_tr_cases] >>
`local_tr (cpu2, spi2) (RX data) (cpu2, spi2')` by METIS_TAC[local_tr_cases] >>
METIS_TAC[global_tr_cases],
`data = SOME spi1.TX_SHIFT_REG` by METIS_TAC[SPI_tx_data] >>
`data <> NONE` by RW_TAC (std_ss++WORD_ss) [] >>
`spi2'.RX_SHIFT_REG = THE data` by METIS_TAC[SPI_rx_data] >>
RW_TAC (std_ss++WORD_ss) []]);

val _ = export_theory();
