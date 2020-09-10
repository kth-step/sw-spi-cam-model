open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open driver_stateTheory board_memTheory;

(* Driver issues a read request to the SPI controller *)
val _ = new_theory "driver_read";

(* dr_read_sysstatus: driver_state -> word32 option * driver_state *)
val dr_read_sysstatus_def = Define `
dr_read_sysstatus (dr:driver_state) =
case dr.dr_init.state of
  | dr_init_idle => (NONE, dr)
  | dr_init_read_req => 
    (SOME SPI0_SYSSTATUS, dr with dr_init := dr.dr_init with state := dr_init_check_rep)
  | dr_init_check_rep => (NONE, dr)
  | dr_init_setting => (NONE, dr)
  | dr_init_done => (NONE, dr)`

(* dr_read_ch0stat: driver_state -> word32 option * driver_state *)
val dr_read_ch0stat_def = Define `
dr_read_ch0stat (dr:driver_state) =
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_read_txs) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME SPI0_CH0STAT, dr with dr_tx := dr.dr_tx with state := dr_tx_check_txs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_read_eot) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME SPI0_CH0STAT, dr with dr_tx := dr.dr_tx with state := dr_tx_check_eot)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_read_rxs) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME SPI0_CH0STAT, dr with dr_rx := dr.dr_rx with state := dr_rx_check_rxs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_txs) then
   (SOME SPI0_CH0STAT, dr with dr_xfer := dr.dr_xfer with state := dr_xfer_check_txs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_rxs) then
   (SOME SPI0_CH0STAT, dr with dr_xfer := dr.dr_xfer with state := dr_xfer_check_rxs)
else (NONE, dr)`

(* dr_read_rx0: driver_state -> word32 option * driver_state *)
val dr_read_rx0_def = Define `
dr_read_rx0 (dr:driver_state) =
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_read_rx0) /\ (dr.dr_xfer.state = dr_xfer_idle) 
then (SOME SPI0_RX0, dr with dr_rx := dr.dr_rx with state := dr_rx_fetch_data)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_rx0) 
then (SOME SPI0_RX0, dr with dr_xfer := dr.dr_xfer with state := dr_xfer_fetch_dataI)
else (NONE, dr)`

(* INIT_RD_ENABLE: driver_state -> bool *)
val INIT_RD_ENABLE_def = Define ` 
INIT_RD_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_read_req) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* TX_RD_ENABLE: driver_state -> bool *)
val TX_RD_ENABLE_def = Define `
TX_RD_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_read_txs \/ dr.dr_tx.state = dr_tx_read_eot) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* RX_RD_ENABLE: driver_state -> bool *)
val RX_RD_ENABLE_def = Define `
RX_RD_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_read_rxs \/ dr.dr_rx.state = dr_rx_read_rx0) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* XFER_RD_ENABLE: driver_state -> bool *)
val XFER_RD_ENABLE_def = Define `
XFER_RD_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_read_txs \/ dr.dr_xfer.state = dr_xfer_read_rxs \/ 
dr.dr_xfer.state = dr_xfer_read_rx0))`

(* dr_read: driver_state -> word32 option * driver_state *)
val dr_read_def = Define `
dr_read (dr:driver_state) =
if dr.dr_err then (NONE, dr)
else if (INIT_RD_ENABLE dr) then (dr_read_sysstatus dr)
else if (TX_RD_ENABLE dr) /\ (dr.dr_tx.state = dr_tx_read_txs \/ dr.dr_tx.state = dr_tx_read_eot)
then (dr_read_ch0stat dr)
else if (RX_RD_ENABLE dr) /\ (dr.dr_rx.state = dr_rx_read_rxs)
then (dr_read_ch0stat dr)
else if (RX_RD_ENABLE dr) /\ (dr.dr_rx.state = dr_rx_read_rx0)
then (dr_read_rx0 dr)
else if (XFER_RD_ENABLE dr) /\ (dr.dr_xfer.state = dr_xfer_read_txs \/ dr.dr_xfer.state = dr_xfer_read_rxs)
then (dr_read_ch0stat dr)
else if (XFER_RD_ENABLE dr) /\ (dr.dr_xfer.state = dr_xfer_read_rx0)
then (dr_read_rx0 dr)
else (NONE, dr)`

val _ = export_theory();
