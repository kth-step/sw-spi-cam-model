open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory SPI_relationTheory;
open driver_stateTheory driver_checkTheory driver_writeTheory driver_readTheory driver_callTheory;

val _ = new_theory "driver_relation";

(* driver_tr: SPI driver transiton relation *)
val (driver_tr_rules, driver_tr_ind, driver_tr_cases) = Hol_reln `
(* driver interal operation, check the reply from the controller *)
(!(dr:driver_state). (DR_TAU_ENABLE dr) /\ (dr.dr_last_read_ad = SOME a) /\ 
(dr.dr_last_read_v = SOME v) ==> 
driver_tr dr tau (dr_check dr a v)) /\
(* driver controls the spi hardware: read and write memory-mapped registers *)
(!(dr:driver_state). (DR_WR_ENABLE dr) ==> 
driver_tr dr (Write (THE (dr_write_address dr)) (THE (dr_write_value dr))) (dr_write_state dr)) /\
(!(dr:driver_state). (DR_RD_ENABLE dr) ==> 
driver_tr dr (Read (THE (dr_read dr).dr_last_read_ad) v) 
((dr_read dr) with dr_last_read_v := SOME v)) /\
(* interface for other programs to call driver's functions *)
(!(dr:driver_state). (dr.state = dr_init_pre \/ dr.state = dr_ready) ==>
driver_tr dr call_init (call_init_dr dr)) /\
(!(dr:driver_state). (dr.state = dr_ready) /\ (buffer <> []) ==>
driver_tr dr (call_tx buffer) (call_tx_dr dr buffer)) /\
(!(dr:driver_state). (dr.state = dr_ready) /\ (length > 0) ==>
driver_tr dr (call_rx length) (call_rx_dr dr length)) /\
(!(dr:driver_state). (dr.state = dr_ready) /\ (buffer <> []) ==>
driver_tr dr (call_xfer buffer) (call_xfer_dr dr buffer)) /\
(!(dr:driver_state). (dr.state = dr_rx_sendback) \/ (dr.state = dr_xfer_sendback) ==>
driver_tr dr (call_back (call_back_dr_data dr)) (call_back_dr_state dr))`

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
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (call_back buffer) dr') ==>
local_tr (dr, spi) (call_back buffer) (dr', spi)) /\
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

(* global_tr: two SPI drivers with each own SPI controller, transition relation *)
val (global_tr_rules, global_tr_ind, global_tr_cases) = Hol_reln `
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) call_init (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) call_init (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_tx buffer) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_tx buffer) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_rx length) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_rx length) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_xfer buffer) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_xfer buffer) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) (call_back buffer) (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) (call_back buffer) (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr1, spi1) tau (dr1', spi1') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2, spi2)) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
local_tr (dr2, spi2) tau (dr2', spi2') ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1, spi1, dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (TX data) (dr1', spi1')) /\
(local_tr (dr2, spi2) (RX data) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (RX data) (dr1', spi1')) /\
(local_tr (dr2, spi2) (TX data) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2', spi2')) /\
(!(dr1:driver_state) (spi1:spi_state) (dr2:driver_state) (spi2:spi_state).
(local_tr (dr1, spi1) (XFER dataI dataO) (dr1', spi1')) /\
(local_tr (dr2, spi2) (XFER dataO dataI) (dr2', spi2')) ==>
global_tr (dr1, spi1, dr2, spi2) tau (dr1', spi1', dr2', spi2'))`

val _ = export_theory();
