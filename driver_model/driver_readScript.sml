open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open driver_stateTheory board_memTheory;

val _ = new_theory "driver_read";

(* DR_RD_ENABLE: driver is in a state that can issue read requests.  *)
val DR_RD_ENABLE_def = Define ` 
DR_RD_ENABLE (dr:driver_state) =
(dr.state = dr_init_read_req \/
dr.state = dr_tx_idle \/
dr.state = dr_tx_read_txs \/
dr.state = dr_tx_read_eot \/
dr.state = dr_tx_read_conf \/
dr.state = dr_rx_idle \/
dr.state = dr_rx_read_rxs \/
dr.state = dr_rx_read_rx0 \/
dr.state = dr_rx_read_conf \/
dr.state = dr_xfer_idle \/
dr.state = dr_xfer_read_txs \/
dr.state = dr_xfer_read_rxs \/
dr.state = dr_xfer_read_rx0 \/
dr.state = dr_xfer_read_conf)`

(* dr_read_sysstatus: read the SYSTATUS register. *)
val dr_read_sysstatus_def = Define `
dr_read_sysstatus (dr:driver_state) =
dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS |>`

(* dr_read_ch0stat: read the CH0STATE register. *)
val dr_read_ch0stat_def = Define `
dr_read_ch0stat (dr:driver_state) =
if (dr.state = dr_tx_read_txs) then 
dr with <| state := dr_tx_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.state = dr_tx_read_eot) then
dr with <| state := dr_tx_check_eot;
dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.state = dr_rx_read_rxs) then
dr with <| state := dr_rx_check_rxs;
dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.state = dr_xfer_read_txs) then
dr with <| state := dr_xfer_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>
else if (dr.state = dr_xfer_read_rxs) then
dr with <| state := dr_xfer_check_rxs;
dr_last_read_ad := SOME SPI0_CH0STAT |>
else dr with dr_err := T`

(* dr_read_ch0conf: read the CH0CONF register. *)
val dr_read_ch0conf_def = Define `
dr_read_ch0conf (dr:driver_state) =
if dr.state = dr_tx_idle then
dr with <| state := dr_tx_fetch_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else if dr.state = dr_tx_read_conf then
dr with <| state := dr_tx_reset_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else if dr.state = dr_rx_idle then
dr with <| state := dr_rx_fetch_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else if dr.state = dr_rx_read_conf then
dr with <| state := dr_rx_reset_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else if dr.state = dr_xfer_idle then
dr with <| state := dr_xfer_fetch_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else if dr.state = dr_xfer_read_conf then
dr with <| state := dr_xfer_reset_conf;
dr_last_read_ad := SOME SPI0_CH0CONF |>
else dr with dr_err := T`

(* dr_read_rx0: read the RX0 register. *)
val dr_read_rx0_def = Define `
dr_read_rx0 (dr:driver_state) =
if dr.state = dr_rx_read_rx0 then 
dr with <| state := dr_rx_fetch_data;
dr_last_read_ad := SOME SPI0_RX0 |>
else if dr.state = dr_xfer_read_rx0 then 
dr with <| state := dr_xfer_fetch_dataI;
dr_last_read_ad := SOME SPI0_RX0 |>
else dr with dr_err := T`

(* dr_read: driver issues a read command to the controller. *)
val dr_read_def = Define `
dr_read (dr:driver_state) =
case dr.state of
  | dr_init_pre => dr with dr_err := T
  | dr_init_idle => dr with dr_err := T  
  | dr_init_read_req => (dr_read_sysstatus dr)
  | dr_init_check_rep => dr with dr_err := T
  | dr_init_setting => dr with dr_err := T
  | dr_ready => dr with dr_err := T
  | dr_tx_idle => dr_read_ch0conf dr
  | dr_tx_fetch_conf => dr with dr_err := T
  | dr_tx_conf_issued => dr with dr_err := T
  | dr_tx_read_txs => dr_read_ch0stat dr
  | dr_tx_check_txs => dr with dr_err := T
  | dr_tx_write_data => dr with dr_err := T
  | dr_tx_read_eot => dr_read_ch0stat dr
  | dr_tx_check_eot => dr with dr_err := T
  | dr_tx_issue_disable => dr with dr_err := T
  | dr_tx_read_conf => dr_read_ch0conf dr
  | dr_tx_reset_conf => dr with dr_err := T
  | dr_rx_idle => dr_read_ch0conf dr
  | dr_rx_fetch_conf => dr with dr_err := T
  | dr_rx_conf_issued => dr with dr_err := T
  | dr_rx_read_rxs => dr_read_ch0stat dr
  | dr_rx_check_rxs => dr with dr_err := T
  | dr_rx_read_rx0 => dr_read_rx0 dr
  | dr_rx_fetch_data => dr with dr_err := T
  | dr_rx_issue_disable => dr with dr_err := T
  | dr_rx_read_conf => dr_read_ch0conf dr
  | dr_rx_reset_conf => dr with dr_err := T
  | dr_rx_sendback => dr with dr_err := T
  | dr_xfer_idle => dr_read_ch0conf dr
  | dr_xfer_fetch_conf => dr with dr_err := T
  | dr_xfer_conf_issued => dr with dr_err := T
  | dr_xfer_read_txs => (dr_read_ch0stat dr)
  | dr_xfer_check_txs => dr with dr_err := T
  | dr_xfer_write_dataO => dr with dr_err := T
  | dr_xfer_read_rxs => (dr_read_ch0stat dr)
  | dr_xfer_check_rxs => dr with dr_err := T
  | dr_xfer_read_rx0 => (dr_read_rx0 dr)
  | dr_xfer_fetch_dataI => dr with dr_err := T
  | dr_xfer_issue_disable => dr with dr_err := T
  | dr_xfer_read_conf => dr_read_ch0conf dr
  | dr_xfer_reset_conf => dr with dr_err := T
  | dr_xfer_sendback => dr with dr_err := T`

val _ = export_theory();
