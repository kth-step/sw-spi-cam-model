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

(* driver_tr: SPI driver transiton relation *)
val (driver_tr_rules, driver_tr_ind, driver_tr_cases) = Hol_reln `
(!(dr:driver_state). (dr.dr_last_read_ad = SOME a) /\ (dr.dr_last_read_v = SOME v) ==> 
driver_tr dr tau (dr_check dr a v)) /\
(!(dr:driver_state). ((INIT_WR_ENABLE dr) \/ (TX_WR_ENABLE dr) \/ (RX_WR_ENABLE dr) \/ 
(XFER_WR_ENABLE dr)) /\ (dr_write_address dr = SOME a) /\ (dr_write_value dr = SOME v) ==> 
driver_tr dr (Write a v) (dr_write_state dr)) /\
(!(dr:driver_state). ((INIT_RD_ENABLE dr) \/ (TX_RD_ENABLE dr) \/ (RX_RD_ENABLE dr) \/
(XFER_RD_ENABLE dr)) /\ ((dr_read dr).dr_last_read_ad = SOME a) ==> 
driver_tr dr (Read a v) ((dr_read dr) with dr_last_read_v := SOME v)) /\
(!(dr:driver_state). (dr.dr_init.state = dr_init_pre) ==>
driver_tr dr call_init (call_init_dr dr)) /\
(!(dr:driver_state). (dr.dr_tx.state = dr_tx_pre) /\ (buffer <> []) ==>
driver_tr dr (call_tx buffer) (call_tx_dr dr buffer)) /\
(!(dr:driver_state). (dr.dr_rx.state = dr_rx_pre) /\ (length > 0) ==>
driver_tr dr (call_rx length) (call_rx_dr dr length)) /\
(!(dr:driver_state). (dr.dr_xfer.state = dr_xfer_pre) /\ (buffer <> []) ==>
driver_tr dr (call_xfer buffer) (call_xfer_dr dr buffer))`

(* local_tr: a driver and an SPI conroller transition *)
val (local_tr_rules, local_tr_ind, local_tr_cases) = Hol_reln `
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
driver_tr dr tau dr' ==> local_tr (dr, spi) tau (dr', spi)) /\
(!(dr:driver_state) (spi:spi_state).
spi_tr spi tau spi' ==> local_tr (dr, spi) tau (dr, spi')) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (Write a v) dr') /\ 
(spi_tr spi (Update a v) spi') ==>
local_tr (dr, spi) tau (dr', spi')) /\
(!(dr:driver_state) (spi:spi_state).
(driver_tr dr (Read a v) dr') /\
(spi_tr spi (Return a v) spi') ==>
local_tr (dr, spi) tau (dr', spi')) /\
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
