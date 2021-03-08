open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_update_regsTheory SPI_return_regsTheory SPI_tauTheory SPI_data_trTheory;

val _ = new_theory "SPI_relation";

(* spi_tr: relation for spi transition (an SPI device). *)
val (spi_tr_rules, spi_tr_ind, spi_tr_cases) = Hol_reln `
(* update the SPI register or return the value: the interface for driver and SPI controller *)
(!(spi:spi_state). T ==> spi_tr spi (Update a v) (write_SPI_regs a v spi)) /\
(!(spi:spi_state). T ==> spi_tr spi 
(Return a (read_SPI_regs_value a spi)) (read_SPI_regs_state a spi)) /\
(* spi internal operation *)
(!(spi:spi_state). (SPI_TAU_ENABLE spi) ==> spi_tr spi tau (spi_tau_operations spi)) /\
(* TX, RX and XFER: 3 cases for spi to transfer data with another spi device *)
(!(spi:spi_state). (spi.state = tx_trans_done \/ spi.state = tx_trans_next) ==> 
spi_tr spi (TX (tx_TX_op_value spi)) (tx_TX_op_state spi)) /\
(!(spi:spi_state). (spi.state = rx_receive_data) /\ (data <> NONE) ==> 
spi_tr spi (RX data) (rx_receive_data_op spi data)) /\
(!(spi:spi_state). (spi.state = xfer_exchange_data) /\ (dataIN <> NONE) ==>
spi_tr spi (XFER dataIN (xfer_exchange_data_op_value spi dataIN)) (xfer_exchange_data_op_state spi dataIN))`

(* spi_cb_tr: a relation for two spi controllers to test data interactions. *)
val (spi_cb_tr_rules, spi_cb_tr_ind, spi_cb_tr_cases) = Hol_reln `
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi1 (Update a v) spi1' ==>
spi_cb_tr (spi1, spi2) (spi1', spi2)) /\
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi1 (Rerurn a v) spi1' ==>
spi_cb_tr (spi1, spi2) (spi1', spi2)) /\
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi1 tau spi1' ==>
spi_cb_tr (spi1, spi2) (spi1', spi2)) /\
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi2 (Update a v) spi2' ==>
spi_cb_tr (spi1, spi2) (spi1, spi2')) /\
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi2 (Rerurn a v) spi2' ==>
spi_cb_tr (spi1, spi2) (spi1, spi2')) /\
(!(spi1:spi_state) (spi2:spi_state). spi_tr spi2 tau spi2' ==>
spi_cb_tr (spi1, spi2) (spi1, spi2')) /\
(!(spi1:spi_state) (spi2:spi_state). (spi_tr spi1 (TX d) spi1') /\ (spi_tr spi2 (RX d) spi2') ==>
spi_cb_tr (spi1, spi2) (spi1', spi2')) /\
(!(spi1:spi_state) (spi2:spi_state). (spi_tr spi1 (RX d) spi1') /\ (spi_tr spi2 (TX d) spi2') ==>
spi_cb_tr (spi1, spi2) (spi1', spi2')) /\
(!(spi1:spi_state) (spi2:spi_state). 
(spi_tr spi1 (XFER d0 d1) spi1') /\ (spi_tr spi2 (XFER d1 d0) spi2') ==>
spi_cb_tr (spi1, spi2) (spi1', spi2'))`

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
