open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory listTheory;
open driver_stateTheory board_memTheory;

(* Driver checks the reply from the SPI controller for a read request *)
val _ = new_theory "driver_check";

(* INIT_CHECK_ENABLE: driver_state -> bool *)
val INIT_CHECK_ENABLE_def = Define `
INIT_CHECK_ENABLE (dr:driver_state) =
(dr.dr_init.state = dr_init_check_rep)`

(* TX_CHECK_ENABLE: driver_state -> bool *)
val TX_CHECK_ENABLE_def = Define `
TX_CHECK_ENABLE (dr:driver_state) =
((dr.dr_tx.state = dr_tx_check_txs) \/
(dr.dr_tx.state = dr_tx_check_eot))`

(* RX_CHECK_ENABLE: driver_state -> bool *)
val RX_CHECK_ENABLE_def = Define `
RX_CHECK_ENBALE (dr:driver_state) =
((dr.dr_rx.state = dr_rx_check_rxs) \/
(dr.dr_rx.state = dr_rx_fetch_data))`

(* XFER_CHECK_ENABLE: driver_state -> bool *)
val XFER_CHECK_ENABLE_def = Define `
XFER_CHECK_ENABLE (dr:driver_state) =
((dr.dr_xfer.state = dr_xfer_check_txs) \/
(dr.dr_xfer.state = dr_xfer_check_rxs) \/
(dr.dr_xfer.state = dr_xfer_fetch_dataI))`

(* CHECK_ENABLE: driver_state -> bool *)
val CHECK_ENABLE_def = Define `
CHECK_ENABLE (dr:driver_state) =
((INIT_CHECK_ENABLE dr) \/ (TX_CHECK_ENABLE dr) \/ 
(RX_CHECK_ENABLE dr) \/ (XFER_CHECK_ENABLE dr))`

(* dr_check_sysstatus:driver_state -> word32 -> driver_state *)
val dr_check_sysstatus_def = Define `
dr_check_sysstatus (dr:driver_state) (rep_v:word32) =
let v = (0 >< 0) rep_v:word1 in
case dr.dr_init.state of
  | dr_init_pre => dr
  | dr_init_idle => dr
  | dr_init_read_req => dr
  | dr_init_check_rep => if v = 1w 
    then dr with <| dr_init := dr.dr_init with state := dr_init_setting;
    dr_tx := dr.dr_tx with state := dr_tx_not_ready;
    dr_rx := dr.dr_rx with state := dr_rx_not_ready;
    dr_xfer := dr.dr_xfer with state := dr_xfer_not_ready |>
    else dr with dr_init := dr.dr_init with state := dr_init_read_req
  | dr_init_setting => dr
  | dr_init_done => dr`

(* dr_check_tx_ch0stat:driver_state -> word32 -> driver_state *)
val dr_check_tx_ch0stat_def = Define `
dr_check_tx_ch0stat (dr:driver_state) (rep_v:word32) =
let v1 = (1 >< 1) rep_v:word1 and
    v2 = (2 >< 2) rep_v:word1 in
case dr.dr_tx.state of
  | dr_tx_not_ready => dr
  | dr_tx_pre => dr
  | dr_tx_idle => dr
  | dr_tx_conf_issued => dr 
  | dr_tx_read_txs => dr
  | dr_tx_check_txs => if v1 = 1w
    then dr with dr_tx := dr.dr_tx with state := dr_tx_write_data
    else dr with dr_tx := dr.dr_tx with state := dr_tx_read_txs
  | dr_tx_write_data => dr
  | dr_tx_read_eot => dr
  | dr_tx_check_eot => if (v1 = 1w) /\ (v2 = 1w)
    then dr with dr_tx := dr.dr_tx with state := dr_tx_issue_disable
    else dr with dr_tx := dr.dr_tx with state := dr_tx_read_eot
  | dr_tx_issue_disable => dr 
  | dr_tx_reset_conf => dr`

(* dr_check_rx_ch0stat:driver_state -> word32 -> driver_state *)
val dr_check_rx_ch0stat_def = Define `
dr_check_rx_ch0stat (dr:driver_state) (rep_v:word32) =
let v = (0 >< 0) rep_v:word1 in
case dr.dr_rx.state of
  | dr_rx_idle => dr 
  | dr_rx_conf_issued => dr
  | dr_rx_read_rxs => dr
  | dr_rx_check_rxs => if v = 1w
    then dr with dr_rx := dr.dr_rx with state := dr_rx_read_rx0
    else dr with dr_rx := dr.dr_rx with state := dr_rx_read_rxs
  | dr_rx_read_rx0 => dr
  | dr_rx_fetch_data => dr
  | dr_rx_issue_diable => dr
  | dr_rx_reset_conf => dr`

(* dr_check_xfer_ch0stat:driver_state -> word32 -> driver_state *)
val dr_check_xfer_ch0stat_def = Define `
dr_check_xfer_ch0stat (dr:driver_state) (rep_v:word32) =
let rxs = (0 >< 0) rep_v:word1 and
    txs = (1 >< 1) rep_v:word1 in
case dr.dr_xfer.state of
  | dr_xfer_idle => dr
  | dr_xfer_conf_issued => dr
  | dr_xfer_read_txs => dr
  | dr_xfer_check_txs => if txs = 1w 
    then dr with dr_xfer := dr.dr_xfer with state := dr_xfer_write_dataO
    else dr with dr_xfer := dr.dr_xfer with state := dr_xfer_read_txs
  | dr_xfer_write_dataO => dr
  | dr_xfer_read_rxs => dr
  | dr_xfer_check_rxs => if rxs = 1w
    then dr with dr_xfer := dr.dr_xfer with state := dr_xfer_read_rx0
    else dr with dr_xfer := dr.dr_xfer with state := dr_xfer_read_rxs
  | dr_xfer_read_rx0 => dr
  | dr_xfer_fetch_dataI => dr
  | dr_xfer_issue_disable => dr
  | dr_xfer_reset_conf => dr`

(* dr_check_ch0stat:driver_state -> word32 -> driver_state *)
val dr_check_ch0stat_def = Define `
dr_check_ch0stat (dr:driver_state) (rep_v:word32) =
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state <> dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle)
then (dr_check_tx_ch0stat dr rep_v)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state <> dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle)
then (dr_check_rx_ch0stat dr rep_v)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state <> dr_xfer_idle)
then (dr_check_xfer_ch0stat dr rep_v)
(* other states cannot process this reply *)
else dr`

(* dr_check_rx0:driver_state -> word32 -> driver_state *)
val dr_check_rx0_def = Define `
dr_check_rx0 (dr:driver_state) (rep_v:word32) =
let v = (7 >< 0) rep_v:word8 in
if (dr.dr_rx.state = dr_rx_fetch_data) /\ (dr.dr_rx.rx_left_length > 1)
then dr with dr_rx := dr.dr_rx with 
     <|state := dr_rx_read_rxs; rx_data_buf := dr.dr_rx.rx_data_buf ++ [v];
       rx_left_length := dr.dr_rx.rx_left_length - 1|>
else if (dr.dr_rx.state = dr_rx_fetch_data) /\ (dr.dr_rx.rx_left_length = 1)
then dr with dr_rx := dr.dr_rx with state := dr_rx_issue_disable
else if (dr.dr_xfer.state = dr_xfer_fetch_dataI)
then dr with dr_xfer := dr.dr_xfer with
     <|state := if (dr.dr_xfer.xfer_cur_length < (LENGTH dr.dr_xfer.xfer_dataOUT_buf)) 
                then dr_xfer_read_txs else dr_xfer_issue_disable; 
       xfer_dataIN_buf := dr.dr_xfer.xfer_dataIN_buf ++ [v]|>
else dr`

(* dr_check:driver_state -> word32 -> word32 -> driver_state *)
val dr_check_def = Define `
dr_check (dr:driver_state) (rep_ad:word32) (rep_v:word32) =
(* driver is in an error state *)
if dr.dr_err then dr
(* only SYSSTATUS, CHOSTAT, RX0 should be hanled *)
else if rep_ad = SPI0_SYSSTATUS then (dr_check_sysstatus dr rep_v)
else if rep_ad = SPI0_CH0STAT then (dr_check_ch0stat dr rep_v)
else if rep_ad = SPI0_RX0 then (dr_check_rx0 dr rep_v)
(* address not handled *)
else dr`

val _ = export_theory();
