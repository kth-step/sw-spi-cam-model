open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory listTheory;
open driver_stateTheory board_memTheory;

val _ = new_theory "driver_check";

(* DR_TAU_ENABLE: driver's state that can perform internal operations. *)
val DR_TAU_ENABLE_def = Define `
DR_TAU_ENABLE (dr:driver_state) =
(dr.state = dr_init_check_rep \/
dr.state = dr_tx_check_txs \/
dr.state = dr_tx_check_eot \/
dr.state = dr_rx_check_rxs \/
dr.state = dr_rx_fetch_data \/
dr.state = dr_xfer_check_txs \/
dr.state = dr_xfer_check_rxs \/
dr.state = dr_xfer_fetch_dataI)`

(* dr_check_sysstatus: check the value of SYSSTATUS register. *)
val dr_check_sysstatus_def = Define `
dr_check_sysstatus (dr:driver_state) (rep_v:word32) =
let v = (0 >< 0) rep_v:word1 in
if v = 1w (* RESET is done *) 
then dr with state := dr_init_setting
else dr with state := dr_init_read_req`

(* dr_check_tx_ch0stat: check the value of CH0STAT register, when in tx mode. *)
val dr_check_tx_ch0stat_def = Define `
dr_check_tx_ch0stat (dr:driver_state) (rep_v:word32) =
let v1 = (1 >< 1) rep_v:word1 and
    v2 = (2 >< 2) rep_v:word1 in
if (dr.state = dr_tx_check_txs) /\ (v1 = 1w) then 
dr with state := dr_tx_write_data
else if (dr.state = dr_tx_check_txs) /\ (v1 = 0w) then
dr with state := dr_tx_read_txs
else if (dr.state = dr_tx_check_eot) /\ (v2 = 1w) /\ (v1 = 1w) then
dr with state := dr_tx_issue_disable
else if (dr.state = dr_tx_check_eot) /\ (~((v2 = 1w) /\ (v1 = 1w))) then
dr with state := dr_tx_read_eot
else dr with dr_err := T`

(* dr_check_rx_ch0stat: check the value of CH0STAT register, when in rx mode. *)
val dr_check_rx_ch0stat_def = Define `
dr_check_rx_ch0stat (dr:driver_state) (rep_v:word32) =
let v = (0 >< 0) rep_v:word1 in
if (v = 1w) /\ (dr.dr_rx.rx_left_length > 0)
then dr with state := dr_rx_read_rx0
else if (v = 1w)
then dr with state := dr_rx_issue_disable
else dr with state := dr_rx_read_rxs`

(* dr_check_xfer_ch0stat: check the value of CH0STAT register, when in xfer mode. *)
val dr_check_xfer_ch0stat_def = Define `
dr_check_xfer_ch0stat (dr:driver_state) (rep_v:word32) =
let rxs = (0 >< 0) rep_v:word1 and
    txs = (1 >< 1) rep_v:word1 in
if (dr.state = dr_xfer_check_txs) /\ (txs = 1w) then 
dr with state := dr_xfer_write_dataO
else if (dr.state = dr_xfer_check_txs) /\ (txs = 0w) then
dr with state := dr_xfer_read_txs
else if (dr.state = dr_xfer_check_rxs) /\ (rxs = 1w) then
dr with state := dr_xfer_read_rx0
else if (dr.state = dr_xfer_check_rxs) /\ (rxs = 0w) then
dr with state := dr_xfer_read_rxs
else dr with dr_err := T`

(* dr_check_rx0: fetch the data of RX0 register. *)
val dr_check_rx0_def = Define `
dr_check_rx0 (dr:driver_state) (rep_v:word32) =
let v = (7 >< 0) rep_v:word8 in
if (dr.state = dr_rx_fetch_data) then
dr with <| dr_rx := dr.dr_rx with <| rx_data_buf := dr.dr_rx.rx_data_buf ++ [v];
rx_left_length := dr.dr_rx.rx_left_length - 1 |>;
state := dr_rx_read_rxs |>
else if (dr.state = dr_xfer_fetch_dataI) then
dr with <| dr_xfer := dr.dr_xfer with xfer_dataIN_buf := dr.dr_xfer.xfer_dataIN_buf ++ [v];
state := if (dr.dr_xfer.xfer_cur_length < (LENGTH dr.dr_xfer.xfer_dataOUT_buf)) 
then dr_xfer_read_txs else dr_xfer_issue_disable |>
else dr with dr_err := T`

(* dr_check: driver's internal operations *)
val dr_check_def = Define `
dr_check (dr:driver_state) (ad:word32) (v:word32) =
case dr.state of
  | dr_init_pre => dr with dr_err := T
  | dr_init_idle => dr with dr_err := T
  | dr_init_read_req => dr with dr_err := T
  | dr_init_check_rep => if (ad = SPI0_SYSSTATUS) then (dr_check_sysstatus dr v)
    else dr with dr_err := T
  | dr_init_setting => dr with dr_err := T
  | dr_ready => dr with dr_err := T
  | dr_tx_idle => dr with dr_err := T
  | dr_tx_fetch_conf => dr with dr_err := T
  | dr_tx_conf_issued => dr with dr_err := T
  | dr_tx_read_txs => dr with dr_err := T
  | dr_tx_check_txs => if (ad = SPI0_CH0STAT) then (dr_check_tx_ch0stat dr v)
    else dr with dr_err := T
  | dr_tx_write_data => dr with dr_err := T
  | dr_tx_read_eot => dr with dr_err := T 
  | dr_tx_check_eot => if (ad = SPI0_CH0STAT) then (dr_check_tx_ch0stat dr v)
    else dr with dr_err := T
  | dr_tx_issue_disable => dr with dr_err := T
  | dr_tx_read_conf => dr with dr_err := T
  | dr_tx_reset_conf => dr with dr_err := T
  | dr_rx_idle => dr with dr_err := T
  | dr_rx_fetch_conf => dr with dr_err := T
  | dr_rx_conf_issued => dr with dr_err := T
  | dr_rx_read_rxs => dr with dr_err := T
  | dr_rx_check_rxs => if (ad = SPI0_CH0STAT) then (dr_check_rx_ch0stat dr v)
    else dr with dr_err := T
  | dr_rx_read_rx0 => dr with dr_err := T
  | dr_rx_fetch_data => if (ad = SPI0_RX0) then (dr_check_rx0 dr v)
    else dr with dr_err := T
  | dr_rx_issue_disable => dr with dr_err := T
  | dr_rx_read_conf => dr with dr_err := T
  | dr_rx_reset_conf => dr with dr_err := T
  | dr_rx_sendback => dr with dr_err := T
  | dr_xfer_idle => dr with dr_err := T
  | dr_xfer_fetch_conf => dr with dr_err := T
  | dr_xfer_conf_issued => dr with dr_err := T
  | dr_xfer_read_txs => dr with dr_err := T
  | dr_xfer_check_txs => if (ad = SPI0_CH0STAT) then (dr_check_xfer_ch0stat dr v)
    else dr with dr_err := T
  | dr_xfer_write_dataO => dr with dr_err := T
  | dr_xfer_read_rxs => dr with dr_err := T
  | dr_xfer_check_rxs => if (ad = SPI0_CH0STAT) then (dr_check_xfer_ch0stat dr v)
    else dr with dr_err := T
  | dr_xfer_read_rx0 => dr with dr_err := T
  | dr_xfer_fetch_dataI => if (ad = SPI0_RX0) then (dr_check_rx0 dr v)
    else dr with dr_err := T
  | dr_xfer_issue_disable => dr with dr_err := T
  | dr_xfer_read_conf => dr with dr_err := T
  | dr_xfet_reset_conf => dr with dr_err := T
  | dr_xfer_sendback => dr with dr_err := T`

val _ = export_theory();
