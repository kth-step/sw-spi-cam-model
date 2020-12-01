open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_checkTheory driver_writeTheory driver_readTheory driver_callTheory;

val _ = new_theory "driver_relation";

(* dr_write_address: driver_state -> word32 option *)
val dr_write_address_def = Define `
dr_write_address (dr:driver_state) =
let (ad, v, dr') = dr_write dr in ad`

(* dr_write_value: driver_state -> word32 option *)
val dr_write_value_def = Define `
dr_write_value (dr:driver_state) =
let (ad, v, dr') = dr_write dr in v`

(* dr_write_state: driver_state -> driver_state *)
val dr_write_state_def = Define `
dr_write_state (dr:driver_state) =
let (ad, v, dr') = dr_write dr in dr'`

(* dr_tx_syn_tr: driver tx automaton synchronizing transtion *)
val (dr_tx_syn_tr_rules, dr_tx_syn_tr_ind, dr_tx_syn_tr_cases) = Hol_reln `
(!(dr_tx:dr_tx_state). dr_tx.state = dr_tx_not_ready ==>
dr_tx_syn_tr dr_tx DR_TX_SYN_RD (dr_tx with state := dr_tx_pre)) /\
(!(dr_tx:dr_tx_state). T ==> dr_tx_syn_tr dr_tx DR_TX_SYN_NRD (dr_tx with state := dr_tx_not_ready))`

(* dr_rx_syn_tr: driver rx automaton synchronizing transition *)
val (dr_rx_syn_tr_rules, dr_rx_syn_tr_ind, dr_rx_syn_tr_cases) = Hol_reln `
(!(dr_rx:dr_rx_state). dr_rx.state = dr_rx_not_ready ==>
dr_rx_syn_tr dr_rx DR_RX_SYN_RD (dr_rx with state := dr_rx_pre)) /\
(!(dr_rx:dr_rx_state). T ==> dr_rx_syn_tr dr_rx DR_RX_SYN_NRD (dr_rx with state := dr_rx_not_ready))`

(* dr_xfer_syn_tr: driver xfer automaton synchronizing transtion *)
val (dr_xfer_syn_tr_rules, dr_xfer_syn_tr_ind, dr_xfer_syn_tr_cases) = Hol_reln `
(!(dr_xfer:dr_xfer_state). dr_xfer.state = dr_xfer_not_ready ==>
dr_xfer_syn_tr dr_xfer DR_XFER_SYN_RD (dr_xfer with state := dr_xfer_pre)) /\
(!(dr_xfer:dr_xfer_state). T ==> dr_xfer_syn_tr dr_xfer DR_XFER_SYN_NRD (dr_xfer with state := dr_xfer_not_ready))`

(* driver_tr: SPI driver transiton relation *)
val (driver_tr_rules, driver_tr_ind, driver_tr_cases) = Hol_reln `
(* driver interal operations for synchronzing *)
(!(dr:driver_state). (dr_tx_syn_tr dr.dr_tx DR_TX_SYN_RD dr_tx') /\ (dr.dr_init.state = dr_init_done) ==>
driver_tr dr tau (dr with dr_tx := dr_tx')) /\
(!(dr:driver_state). (dr_rx_syn_tr dr.dr_rx DR_RX_SYN_RD dr_rx') /\ (dr.dr_init.state = dr_init_done) ==>
driver_tr dr tau (dr with dr_rx := dr_rx')) /\
(!(dr:driver_state). (dr_xfer_syn_tr dr.dr_xfer DR_XFER_SYN_RD dr_xfer') /\ (dr.dr_init.state = dr_init_done) ==>
driver_tr dr tau (dr with dr_xfer := dr_xfer')) /\
(!(dr:driver_state). (dr_tx_syn_tr dr.dr_tx DR_TX_SYN_NRD dr_tx') /\ (dr.dr_init.state = dr_init_idle) ==>
driver_tr dr tau (dr with dr_tx := dr_tx')) /\
(!(dr:driver_state). (dr_rx_syn_tr dr.dr_rx DR_RX_SYN_NRD dr_rx') /\ (dr.dr_init.state = dr_init_idle) ==>
driver_tr dr tau (dr with dr_rx := dr_rx')) /\
(!(dr:driver_state). (dr_xfer_syn_tr dr.dr_xfer DR_XFER_SYN_NRD dr_xfer') /\ (dr.dr_init.state = dr_init_idle) ==>
driver_tr dr tau (dr with dr_xfer := dr_xfer')) /\
(* driver interal operation *)
(!(dr:driver_state). (dr.dr_last_read_ad = SOME a) /\ (dr.dr_last_read_v = SOME v) ==> 
driver_tr dr tau (dr_check dr a v)) /\
(* driver controls the spi hardware through Read and Write memory-mapped registers *)
(!(dr:driver_state). ((INIT_WR_ENABLE dr) \/ (TX_WR_ENABLE dr) \/ 
(RX_WR_ENABLE dr) \/ (XFER_WR_ENABLE dr)) ==> 
driver_tr dr 
(Write (THE (dr_write_address dr)) (THE (dr_write_value dr))) (dr_write_state dr)) /\
(!(dr:driver_state). ((INIT_RD_ENABLE dr) \/ (TX_RD_ENABLE dr) \/ 
(RX_RD_ENABLE dr) \/ (XFER_RD_ENABLE dr)) ==> 
driver_tr dr (Read (THE (dr_read dr).dr_last_read_ad) v) 
((dr_read dr) with dr_last_read_v := SOME v)) /\
(* interface for other programs call driver's functions *)
(!(dr:driver_state). (dr.dr_init.state = dr_init_pre \/ dr.dr_init.state = dr_init_done) ==>
driver_tr dr call_init (call_init_dr dr)) /\
(!(dr:driver_state). (dr.dr_tx.state = dr_tx_pre) /\ (buffer <> []) ==>
driver_tr dr (call_tx buffer) (call_tx_dr dr buffer)) /\
(!(dr:driver_state). (dr.dr_rx.state = dr_rx_pre) /\ (length > 0) ==>
driver_tr dr (call_rx length) (call_rx_dr dr length)) /\
(!(dr:driver_state). (dr.dr_xfer.state = dr_xfer_pre) /\ (buffer <> []) ==>
driver_tr dr (call_xfer buffer) (call_xfer_dr dr buffer))`

(* local_tr: a driver and an SPI conroller transition *)
val (local_tr_rules, local_tr_ind, local_tr_cases) = Hol_reln `
(* other programs call driver's functions *)
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr call_init dr') ==> 
local_tr (dr, spi) call_init (dr', spi)) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (call_tx buffer) dr') ==> 
local_tr (dr, spi) (call_tx buffer) (dr', spi)) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (call_rx length) dr') ==>
local_tr (dr, spi) (call_rx length) (dr', spi)) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (call_xfer buffer) dr') ==>
local_tr (dr, spi) (call_xfer buffer) (dr', spi)) /\
(* driver and spi internal operations *)
(!(dr:driver_state) (spi:spi_state).
driver_tr dr tau dr' ==> local_tr (dr, spi) tau (dr', spi)) /\
(!(dr:driver_state) (spi:spi_state).
spi_tr spi tau spi' ==> local_tr (dr, spi) tau (dr, spi')) /\
(* driver and spi interaction *)
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (Write a v) dr') /\ 
(spi_tr spi (Update a v) spi') ==>
local_tr (dr, spi) tau (dr', spi')) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (Read a v) dr') /\
(spi_tr spi (Return a v) spi') ==>
local_tr (dr, spi) tau (dr', spi')) /\
(* spi transforms data with other spi devices *)
(!(dr:driver_state) (spi:spi_state).
spi_tr spi (TX data) spi' ==> local_tr (dr, spi) (TX data) (dr, spi')) /\
(!(dr:driver_state) (spi:spi_state).
(spi_tr spi (RX data) spi') ==> 
local_tr (dr, spi) (RX data) (dr, spi')) /\
(!(dr:driver_state) (spi:spi_state).
spi_tr spi (XFER dataIN dataOUT) spi' ==> local_tr (dr, spi) (XFER dataIN dataOUT) (dr, spi'))`

(* global_tr: two SPI drivers with each own SPI controller, transition relation without labels *)
val (global_tr_rules, global_tr_ind, global_tr_cases) = Hol_reln `
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) call_init (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) call_init (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_tx buffer) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_tx buffer) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_rx length) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_rx length) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_xfer buffer) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_xfer buffer) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) tau (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) tau (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (TX data) (dr1', spi1')) /\
(local_tr (dr2, spi2) (RX data) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (RX data) (dr1', spi1')) /\
(local_tr (dr2, spi2) (TX data) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (XFER dataI dataO) (dr1', spi1')) /\
(local_tr (dr2, spi2) (XFER dataO dataI) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) (dr1', spi1', dr2', spi2'))`

val _ = export_theory();
