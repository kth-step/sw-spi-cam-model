open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory listTheory;
open driver_stateTheory board_memTheory;

(* Driver issues a write request to the SPI controller *)
val _ = new_theory "driver_write";

(* dr_write_softreset: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_softreset_def = Define `
dr_write_softreset (dr:driver_state) =
let addr = SPI0_SYSCONFIG:word32 and
    v = 0x00000002w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (SOME addr, SOME v, 
    dr with dr_init := dr.dr_init with <|state := dr_init_read_req;
    issue_wr_sysconfig := F; issue_wr_modulctrl := F; issue_wr_ch0conf_wl := F;
    issue_wr_ch0conf_mode := F; issue_wr_ch0conf_speed := F |>)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)
  | dr_init_setting => (NONE, NONE, dr)
  | dr_init_done => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|state := dr_init_read_req;
    issue_wr_sysconfig := F; issue_wr_modulctrl := F; issue_wr_ch0conf_wl := F;
    issue_wr_ch0conf_mode := F; issue_wr_ch0conf_speed := F |>)`

(* dr_write_sysconfig: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_sysconfig_def = Define `
dr_write_sysconfig (dr:driver_state) =
let addr = SPI0_SYSCONFIG:word32 and
    v = 0x00000011w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (NONE, NONE, dr)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)
  | dr_init_setting => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|
    issue_wr_sysconfig := T;
    state := if (dr.dr_init.issue_wr_modulctrl) /\
    (dr.dr_init.issue_wr_ch0conf_wl) /\ (dr.dr_init.issue_wr_ch0conf_mode) /\
    (dr.dr_init.issue_wr_ch0conf_speed) then
    dr_init_done else dr_init_setting |>)
  | dr_init_done => (NONE, NONE, dr)`

(* dr_write_modulctrl: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_modulctrl_def = Define `
dr_write_modulctrl (dr:driver_state) =
let addr = SPI0_MODULCTRL:word32 and
    v = 0x00000001w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (NONE, NONE, dr)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)
  | dr_init_setting => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|
    issue_wr_modulctrl := T;
    state :=  if (dr.dr_init.issue_wr_sysconfig) /\
    (dr.dr_init.issue_wr_ch0conf_wl) /\ (dr.dr_init.issue_wr_ch0conf_mode) /\
    (dr.dr_init.issue_wr_ch0conf_speed) then
    dr_init_done else dr_init_setting |>)
  | dr_init_done => (NONE, NONE, dr)`

(* dr_write_ch0conf_wl: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_wl_def = Define `
dr_write_ch0conf_wl (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v = 0x00000380w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (NONE, NONE, dr)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)
  | dr_init_setting => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|
    issue_wr_ch0conf_wl := T;
    state :=  if (dr.dr_init.issue_wr_sysconfig) /\ (dr.dr_init.issue_wr_modulctrl) /\
    (dr.dr_init.issue_wr_ch0conf_mode) /\ (dr.dr_init.issue_wr_ch0conf_speed) then
    dr_init_done else dr_init_setting |>)
  | dr_init_done => (NONE, NONE, dr)`

(* dr_write_ch0conf_mode: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_mode_def = Define `
dr_write_ch0conf_mode (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v = 0x00010040w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (NONE, NONE, dr)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)   
  | dr_init_setting => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|
    issue_wr_ch0conf_mode := T;
    state :=  if (dr.dr_init.issue_wr_sysconfig) /\ (dr.dr_init.issue_wr_modulctrl) /\
    (dr.dr_init.issue_wr_ch0conf_wl) /\ (dr.dr_init.issue_wr_ch0conf_speed) then
    dr_init_done else dr_init_setting |>)
  | dr_init_done => (NONE, NONE, dr)`

(* dr_write_ch0conf_speed: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_speed_def = Define `
dr_write_ch0conf_speed (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v = 0x00000014w:word32 in
case dr.dr_init.state of
  | dr_init_idle => (NONE, NONE, dr)
  | dr_init_read_req => (NONE, NONE, dr)
  | dr_init_check_rep => (NONE, NONE, dr)   
  | dr_init_setting => (SOME addr, SOME v,
    dr with dr_init := dr.dr_init with <|
    issue_wr_ch0conf_speed := T;
    state :=  if (dr.dr_init.issue_wr_sysconfig) /\ (dr.dr_init.issue_wr_modulctrl) /\
    (dr.dr_init.issue_wr_ch0conf_wl) /\ (dr.dr_init.issue_wr_ch0conf_mode) then
    dr_init_done else dr_init_setting |>)
  | dr_init_done => (NONE, NONE, dr)`

(* dr_write_ch0conf_tx: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_tx_def = Define `
dr_write_ch0conf_tx (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1 = 0x00102000w:word32 and
    v2 = 0x00000000w:word32 in
case dr.dr_tx.state of
  | dr_tx_idle => if (dr.dr_tx.data_buf <> []) then
    (SOME addr, SOME v1, 
    dr with dr_tx := dr.dr_tx with 
    <|state := dr_tx_conf_issued; tx_left_length := LENGTH dr.dr_tx.data_buf|>)
    else (NONE, NONE, dr with dr_err := T) 
  | dr_tx_conf_issued => (NONE, NONE, dr)
  | dr_tx_read_txs => (NONE, NONE, dr) 
  | dr_tx_check_txs => (NONE, NONE, dr)
  | dr_tx_write_data => (NONE, NONE, dr)
  | dr_tx_read_eot => (NONE, NONE, dr)
  | dr_tx_check_eot => (NONE, NONE, dr)    
  | dr_tx_issue_disable => (NONE, NONE, dr)
  | dr_tx_reset_conf => (SOME addr, SOME v2,
    dr with dr_tx := dr.dr_tx with state := dr_tx_idle)`

(* dr_write_ch0conf_rx: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_rx_def = Define `
dr_write_ch0conf_rx (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1 = 0x00101000w:word32 and
    v2 = 0x00000000w:word32 in
case dr.dr_rx.state of
  | dr_rx_idle => (SOME addr, SOME v1, 
    dr with dr_rx := dr.dr_rx with
    <|state := dr_rx_conf_issued; rx_data_buf := [];
    rx_left_length := 10 (* Fixed so far, TOCHANGE *)|>)
  | dr_rx_conf_issued => (NONE, NONE, dr)
  | dr_rx_read_rxs => (NONE, NONE, dr)
  | dr_rx_check_rxs => (NONE, NONE, dr)
  | dr_rx_read_rx0 => (NONE, NONE, dr)
  | dr_rx_fetch_data => (NONE, NONE, dr)
  | dr_rx_issue_disable => (NONE, NONE, dr)
  | dr_rx_reset_conf => (SOME addr, SOME v2,
    dr with dr_rx := dr.dr_rx with state := dr_rx_idle)`

(* dr_write_ch0conf_xfer: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0conf_xfer_def = Define `
dr_write_ch0conf_xfer (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1 = 0x00100000w:word32 and
    v2 = 0x00000000w:word32 in
case dr.dr_xfer.state of
 | dr_xfer_idle => if (dr.dr_xfer.xfer_dataOUT_buf <> []) then
   (SOME addr, SOME v1,
    dr with dr_xfer := dr.dr_xfer with
    <|state := dr_xfer_conf_issued; xfer_left_length := LENGTH dr.dr_xfer.xfer_dataOUT_buf;
      xfer_dataIN_buf := []|>)
    else (NONE, NONE, dr with dr_err := T)
 | dr_xfer_conf_issued => (NONE, NONE, dr)
 | dr_xfer_read_txs => (NONE, NONE, dr)
 | dr_xfer_check_txs => (NONE, NONE, dr)
 | dr_xfer_write_dataO => (NONE, NONE, dr)
 | dr_xfer_read_rxs => (NONE, NONE, dr)
 | dr_xfer_check_rxs => (NONE, NONE, dr)
 | dr_xfer_read_rx0 => (NONE, NONE, dr)
 | dr_xfer_fetch_dataI => (NONE, NONE, dr)
 | dr_xfer_issue_disable => (NONE, NONE, dr)
 | dr_xfer_reset_conf => (SOME addr, SOME v2, 
   dr with dr_xfer := dr.dr_xfer with state := dr_xfer_idle)`

(* dr_write_ch0ctrl: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_ch0ctrl_def = Define `
dr_write_ch0ctrl (dr:driver_state) =
let addr = SPI0_CH0CTRL:word32 and
    v1 = 0x00000001w:word32 and
    v2 = 0x00000000w:word32 in
if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_conf_issued) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME addr, SOME v1, 
    dr with dr_tx := dr.dr_tx with state := dr_tx_read_txs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_issue_disable) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME addr, SOME v2, 
    dr with dr_tx := dr.dr_tx with state := dr_tx_reset_conf)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_conf_issued) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME addr, SOME v1,
    dr with dr_rx := dr.dr_rx with state := dr_rx_read_rxs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_issue_disable) /\ (dr.dr_xfer.state = dr_xfer_idle) then
   (SOME addr, SOME v2, 
    dr with dr_rx := dr.dr_rx with state := dr_rx_reset_conf)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_conf_issued) then
   (SOME addr, SOME v1,
    dr with dr_xfer := dr.dr_xfer with state := dr_xfer_read_txs)
else if (dr.dr_init.state = dr_init_done) /\ (dr.dr_tx.state = dr_tx_idle) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_issue_disable) then
   (SOME addr, SOME v2,
   dr with dr_xfer := dr.dr_xfer with state := dr_xfer_reset_conf)
else (NONE, NONE, dr)`

(* dr_write_tx0: driver_state -> word32 option * word32 option * driver_state *)
val dr_write_tx0_def = Define `
dr_write_tx0 (dr:driver_state) = 
if (dr.dr_tx.state = dr_tx_write_data) /\ (dr.dr_init.state = dr_init_done) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) /\
   (dr.dr_tx.tx_left_length > 0)
then (SOME SPI0_TX0, SOME (w2w (HD dr.dr_tx.data_buf):word32),
      dr with dr_tx := dr.dr_tx with 
      <|state := dr_tx_read_txs; data_buf := TL dr.dr_tx.data_buf;
      tx_left_length := dr.dr_tx.tx_left_length - 1|>)
else if (dr.dr_tx.state = dr_tx_write_data) /\ (dr.dr_init.state = dr_init_done) /\
   (dr.dr_rx.state = dr_rx_idle) /\ (dr.dr_xfer.state = dr_xfer_idle) /\
   (dr.dr_tx.tx_left_length = 0)
then (NONE, NONE, dr with dr_tx := dr.dr_tx with state := dr_tx_read_eot)
else if (dr.dr_xfer.state = dr_xfer_write_dataO) /\ (dr.dr_init.state = dr_init_done) /\
    (dr.dr_tx.state = dr_tx_idle) /\ (dr.dr_rx.state = dr_rx_idle) /\
    (dr.dr_xfer.xfer_left_length > 0)
then (SOME SPI0_TX0, SOME (w2w (HD dr.dr_xfer.xfer_dataOUT_buf)),
     dr with dr_xfer := dr.dr_xfer with
     <|state := dr_xfer_read_rxs; xfer_dataOUT_buf := TL dr.dr_xfer.xfer_dataOUT_buf;
     xfer_left_length := dr.dr_xfer.xfer_left_length - 1|>)
else if (dr.dr_xfer.state = dr_xfer_write_dataO) /\ (dr.dr_init.state = dr_init_done) /\
    (dr.dr_tx.state = dr_tx_idle) /\ (dr.dr_rx.state = dr_rx_idle) /\
    (dr.dr_xfer.xfer_left_length = 0)
then (NONE, NONE, dr with dr_err := T)
else (NONE, NONE, dr)`

(* INIT_WR_ENABLE:driver_state -> bool
 * driver is eligible to issue write commands within init state.
 *)
val INIT_WR_ENABLE_def = Define `
INIT_WR_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_idle \/ dr.dr_init.state = dr_init_setting 
\/ dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* TX_WR_ENABLE:driver_state -> bool
 * driver is eligible to issue write commands within tx state.
 *)
val TX_WR_ENABLE_def = Define `
TX_WR_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle \/ dr.dr_tx.state = dr_tx_conf_issued \/ 
dr.dr_tx.state = dr_tx_write_data \/ dr.dr_tx.state = dr_tx_issue_disable \/ 
dr_tx_issue_disable = dr_tx_reset_conf) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* RX_WR_ENABLE:driver_state -> bool
 * driver is eligible to issue write commands within rx state.
 *)
val RX_WR_ENABLE_def = Define `
RX_WR_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_idle \/ dr.dr_rx.state = dr_rx_conf_issued \/ 
dr.dr_rx.state = dr_rx_issue_disable \/ dr.dr_rx.state = dr_rx_reset_conf) /\
(dr.dr_xfer.state = dr_xfer_idle))`

(* XFER_WR_ENABLE:driver_state -> bool
 * driver is eligible to issue write commands within xfer state.
 *)
val XFER_WR_ENABLE_def = Define `
XFER_WR_ENABLE (dr:driver_state) =
((dr.dr_init.state = dr_init_done) /\
(dr.dr_tx.state = dr_tx_idle) /\
(dr.dr_rx.state = dr_rx_idle) /\
(dr.dr_xfer.state = dr_xfer_idle \/ dr.dr_xfer.state = dr_xfer_conf_issued \/
dr.dr_xfer.state = dr_xfer_write_dataO \/ dr.dr_xfer.state = dr_xfer_issue_disable \/
dr.dr_xfer.state = dr_xfer_reset_conf))`

(* dr_write:driver_state -> word32 option * word32 option * word32 option *)
val dr_write_def = Define `
dr_write (dr:driver_state) =
if dr.dr_err then (NONE, NONE, dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_idle \/ dr.dr_init.state = dr_init_done) 
then (dr_write_softreset dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_setting) /\ (~ dr.dr_init.issue_wr_sysconfig)
then (dr_write_sysconfig dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_setting) /\ (~ dr.dr_init.issue_wr_modulctrl)
then (dr_write_modulctrl dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_setting) /\ (~ dr.dr_init.issue_wr_ch0conf_wl)
then (dr_write_ch0conf_wl dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_setting) /\ (~ dr.dr_init.issue_wr_ch0conf_mode)
then (dr_write_ch0conf_wl dr)
else if (INIT_WR_ENABLE dr) /\ (dr.dr_init.state = dr_init_setting) /\ (~ dr.dr_init.issue_wr_ch0conf_speed)
then (dr_write_ch0conf_speed dr)
else if (TX_WR_ENABLE dr) /\ (dr.dr_tx.state = dr_tx_idle \/ dr.dr_tx.state = dr_tx_reset_conf)
then (dr_write_ch0conf_tx dr)
else if (TX_WR_ENABLE dr) /\ (dr.dr_tx.state = dr_tx_conf_issued \/ dr.dr_tx.state = dr_tx_issue_disable) 
then (dr_write_ch0ctrl dr)
else if (TX_WR_ENABLE dr) /\ (dr.dr_tx.state = dr_tx_write_data)
then (dr_write_tx0 dr)
else if (RX_WR_ENABLE dr) /\ (dr.dr_rx.state = dr_rx_idle \/ dr.dr_rx.state = dr_rx_reset_conf)
then (dr_write_ch0conf_rx dr)
else if (RX_WR_ENABLE dr) /\ (dr.dr_rx.state = dr_rx_conf_issued \/ dr.dr_rx.state = dr_rx_issue_disable)
then (dr_write_ch0ctrl dr)
else if (XFER_WR_ENABLE dr) /\ (dr.dr_xfer.state = dr_xfer_idle \/ dr.dr_xfer.state = dr_xfer_reset_conf)
then (dr_write_ch0conf_xfer dr)
else if (XFER_WR_ENABLE dr) /\ (dr.dr_xfer.state = dr_xfer_conf_issued \/ dr.dr_xfer.state = dr_xfer_issue_disable)
then (dr_write_ch0ctrl dr)
else if (XFER_WR_ENABLE dr) /\ (dr.dr_xfer.state = dr_xfer_write_dataO)
then (dr_write_tx0 dr)
(* other conditions, no write commands issued *)
else (NONE, NONE, dr)`

val _ = export_theory();
