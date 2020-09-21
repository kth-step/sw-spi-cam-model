open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open driver_stateTheory board_memTheory;

(* Driver issues a read request to the SPI controller, mainly update dr.dr_last_read_ad *)
val _ = new_theory "driver_read";

(* dr_read_sysstatus: driver_state -> driver_state *)
val dr_read_sysstatus_def = Define `
dr_read_sysstatus (dr:driver_state) =
case dr.dr_init.state of
  | dr_init_idle => dr with dr_last_read_ad := NONE
  | dr_init_read_req => 
    dr with <| dr_init := dr.dr_init with state := dr_init_check_rep;
    dr_last_read_ad := SOME SPI0_SYSSTATUS |>
  | dr_init_check_rep => dr with dr_last_read_ad := NONE
  | dr_init_setting => dr with dr_last_read_ad := NONE
  | dr_init_done => dr with dr_last_read_ad := NONE`

(* dr_read_ch0stat: driver_state -> driver_state *)
val dr_read_ch0stat_def = Define `
dr_read_ch0stat (dr:driver_state) =
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_read_txs) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   dr with <| dr_tx := dr.dr_tx with state := dr_tx_check_txs;
   dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_read_eot) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   dr with <| dr_tx := dr.dr_tx with state := dr_tx_check_eot;
   dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_read_rxs) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   dr with <| dr_rx := dr.dr_rx with state := dr_rx_check_rxs;
   dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_txs) then
   dr with <| dr_xfer := dr.dr_xfer with state := dr_xfer_check_txs;
   dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_rxs) then
   dr with <| dr_xfer := dr.dr_xfer with state := dr_xfer_check_rxs;
   dr_last_read_ad := SOME SPI0_CH0STAT |>
else dr with dr_last_read_ad := NONE`

(* dr_read_rx0: driver_state ->  driver_state *)
val dr_read_rx0_def = Define `
dr_read_rx0 (dr:driver_state) =
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_read_rx0) /\ (dr.dr_xfer.state = dr_xfer_idle) 
then dr with <| dr_rx := dr.dr_rx with state := dr_rx_fetch_data;
   dr_last_read_ad := SOME SPI0_RX0 |>
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_read_rx0) 
then dr with <| dr_xfer := dr.dr_xfer with state := dr_xfer_fetch_dataI;
   dr_last_read_ad := SOME SPI0_RX0 |>
else dr with dr_last_read_ad := NONE`

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

(* dr_read: driver_state -> driver_state *)
val dr_read_def = Define `
dr_read (dr:driver_state) =
if dr.dr_err then dr with dr_last_read_ad := NONE
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
else dr with dr_last_read_ad := NONE`

val _ = export_theory();
