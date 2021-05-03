open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory listTheory;
open driver_stateTheory board_memTheory;

val _ = new_theory "driver_write";

(* DR_WR_ENABLE: driver is available to issue write commands. *)
val DR_WR_ENABLE_def = Define `
DR_WR_ENABLE (dr:driver_state) =
(dr.state = dr_init_idle \/
dr.state = dr_init_setting \/
dr.state = dr_tx_fetch_conf \/
dr.state = dr_tx_conf_issued \/ 
dr.state = dr_tx_write_data \/
dr.state = dr_tx_issue_disable \/
dr.state = dr_tx_reset_conf \/
dr.state = dr_rx_fetch_conf \/
dr.state = dr_rx_conf_issued \/
dr.state = dr_rx_issue_disable \/
dr.state = dr_rx_reset_conf \/
dr.state = dr_xfer_fetch_conf \/
dr.state = dr_xfer_conf_issued \/
dr.state = dr_xfer_write_dataO \/
dr.state = dr_xfer_issue_disable \/
dr.state = dr_xfer_reset_conf)`

(* dr_write_softreset: write the SOFTRESET bit. *)
val dr_write_softreset_def = Define `
dr_write_softreset (dr:driver_state) =
let addr = SPI0_SYSCONFIG:word32 and
    v = 0x00000002w:word32 in 
(SOME addr, SOME v, 
dr with <| dr_init := <|issue_wr_sysconfig := F; 
issue_wr_modulctrl := F |>;
state := dr_init_read_req |>)`

(* dr_write_sysconfig: set up the SYSCONFIG register. *)
val dr_write_sysconfig_def = Define `
dr_write_sysconfig (dr:driver_state) =
let addr = SPI0_SYSCONFIG:word32 and
    v = 0x00000011w:word32 in 
(SOME addr, SOME v,
dr with <| dr_init := dr.dr_init with issue_wr_sysconfig := T;
state := dr_init_setting |>)`

(* dr_write_modulctrl: set up the MODULCTRL register. *)
val dr_write_modulctrl_def = Define `
dr_write_modulctrl (dr:driver_state) =
let addr = SPI0_MODULCTRL:word32 and
    v = 0x00000001w:word32 in
(SOME addr, SOME v,
dr with <| dr_init := dr.dr_init with issue_wr_modulctrl := T;
state := dr_init_setting |>)`

(* dr_write_ch0conf_init: set up the ch0conf register *)
val dr_write_ch0conf_init_def = Define `
dr_write_ch0conf_init (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v = 0x000103D8w:word32 in
(SOME addr, SOME v, dr with state := dr_ready)`

(* dr_write_ch0conf_tx: set up the CH0CONF register for tx mode. *)
val dr_write_ch0conf_tx_def = Define `
dr_write_ch0conf_tx (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1:word32 = (THE dr.dr_last_read_v) && (0xFFEFCFFFw:word32) || (0x00102000w:word32) and
    v2:word32 = (THE dr.dr_last_read_v) && (0xFFEFFFFFw:word32) in
if (dr.state = dr_tx_fetch_conf) then
(SOME addr, SOME v1, dr with state := dr_tx_conf_issued)
else if (dr.state = dr_tx_reset_conf) then 
(SOME addr, SOME v2, dr with state := dr_ready)
else (NONE, NONE, dr with dr_err := T)`

(* dr_write_ch0conf_rx: set up the CH0CONF register for rx mode. *)
val dr_write_ch0conf_rx_def = Define `
dr_write_ch0conf_rx (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1:word32 = (THE dr.dr_last_read_v) && (0xFFEFCFFFw:word32) || (0x00101000w:word32) and
    v2:word32 = (THE dr.dr_last_read_v) && (0xFFEFFFFFw:word32) in
if (dr.state = dr_rx_fetch_conf) then
(SOME addr, SOME v1, dr with state := dr_rx_conf_issued)
else if (dr.state = dr_rx_reset_conf) then
(SOME addr, SOME v2, dr with state := dr_rx_sendback)
else (NONE, NONE, dr with dr_err := T)`

(* dr_write_ch0conf_xfer: set up the CH0CONF register for xfer mode. *)
val dr_write_ch0conf_xfer_def = Define `
dr_write_ch0conf_xfer (dr:driver_state) =
let addr = SPI0_CH0CONF:word32 and
    v1:word32 = (THE dr.dr_last_read_v) && (0xFFEFCFFFw:word32) || (0x00100000w:word32) and
    v2:word32 = (THE dr.dr_last_read_v) && (0xFFEFFFFFw:word32) in
if (dr.state = dr_xfer_fetch_conf) then
(SOME addr, SOME v1, dr with state := dr_xfer_conf_issued)
else if (dr.state = dr_xfer_reset_conf) then
(SOME addr, SOME v2, dr with state := dr_xfer_sendback)
else (NONE, NONE, dr with dr_err := T)`

(* dr_write_ch0ctrl: set up the CH0CTRL register. *)
val dr_write_ch0ctrl_def = Define `
dr_write_ch0ctrl (dr:driver_state) =
let addr = SPI0_CH0CTRL:word32 and
    v1 = 0x00000001w:word32 and
    v2 = 0x00000000w:word32 in
if (dr.state = dr_tx_conf_issued) then
(SOME addr, SOME v1, dr with state := dr_tx_read_txs)
else if (dr.state = dr_tx_issue_disable) then
(SOME addr, SOME v2, dr with state := dr_tx_read_conf)
else if (dr.state = dr_rx_conf_issued) then 
(SOME addr, SOME v1, dr with state := dr_rx_read_rxs)
else if (dr.state = dr_rx_issue_disable) then 
(SOME addr, SOME v2, dr with state := dr_rx_read_conf)
else if (dr.state = dr_xfer_conf_issued) then
(SOME addr, SOME v1, dr with state := dr_xfer_read_txs)
else if (dr.state = dr_xfer_issue_disable) then
(SOME addr, SOME v2, dr with state := dr_xfer_read_conf)
else (NONE, NONE, dr with dr_err := T)`

(* dr_write_tx0: write the data to the TX0 register. *)
val dr_write_tx0_def = Define `
dr_write_tx0 (dr:driver_state) = 
if (dr.state = dr_tx_write_data) /\ 
(dr.dr_tx.tx_cur_length < ((LENGTH dr.dr_tx.tx_data_buf) - 1)) then 
(SOME SPI0_TX0, SOME (w2w (EL (dr.dr_tx.tx_cur_length) (dr.dr_tx.tx_data_buf))),
dr with <| dr_tx := dr.dr_tx with tx_cur_length := dr.dr_tx.tx_cur_length + 1;
state := dr_tx_read_txs |>)
else if (dr.state = dr_tx_write_data) /\
(~ (dr.dr_tx.tx_cur_length < ((LENGTH dr.dr_tx.tx_data_buf) - 1))) then 
(SOME SPI0_TX0, SOME (w2w (EL (dr.dr_tx.tx_cur_length) (dr.dr_tx.tx_data_buf))),
dr with <| dr_tx := dr.dr_tx with tx_cur_length := dr.dr_tx.tx_cur_length + 1;
state := dr_tx_read_eot |>)
else if (dr.state = dr_xfer_write_dataO) then 
(SOME SPI0_TX0, SOME (w2w (EL (dr.dr_xfer.xfer_cur_length) (dr.dr_xfer.xfer_dataOUT_buf))),
dr with <| dr_xfer := dr.dr_xfer with xfer_cur_length := dr.dr_xfer.xfer_cur_length + 1;
state := dr_xfer_read_rxs |>)
else (NONE, NONE, dr with dr_err := T)`

(* dr_write: driver issues a write command to the controller. *)
val dr_write_def = Define `
dr_write (dr:driver_state) =
case dr.state of
 | dr_init_pre => (NONE, NONE, dr with dr_err := T)
 | dr_init_idle => (dr_write_softreset dr)
 | dr_init_read_req => (NONE, NONE, dr with dr_err := T)
 | dr_init_check_rep => (NONE, NONE, dr with dr_err := T)
 | dr_init_setting => if (~ dr.dr_init.issue_wr_sysconfig) then (dr_write_sysconfig dr)
                      else if (~ dr.dr_init.issue_wr_modulctrl) then (dr_write_modulctrl dr)
                      else (dr_write_ch0conf_init dr)
 | dr_ready => (NONE, NONE, dr with dr_err := T)
 | dr_tx_idle => (NONE, NONE, dr with dr_err := T)
 | dr_tx_fetch_conf => (dr_write_ch0conf_tx dr)
 | dr_tx_conf_issued => (dr_write_ch0ctrl dr)
 | dr_tx_read_txs => (NONE, NONE, dr with dr_err := T)
 | dr_tx_check_txs => (NONE, NONE, dr with dr_err := T)
 | dr_tx_write_data => (dr_write_tx0 dr)
 | dr_tx_read_eot => (NONE, NONE, dr with dr_err := T)
 | dr_tx_check_eot => (NONE, NONE, dr with dr_err := T)
 | dr_tx_issue_disable => (dr_write_ch0ctrl dr)
 | dr_tx_read_conf => (NONE, NONE, dr with dr_err := T)
 | dr_tx_reset_conf => (dr_write_ch0conf_tx dr)
 | dr_rx_idle => (NONE, NONE, dr with dr_err := T)
 | dr_rx_fetch_conf => (dr_write_ch0conf_rx dr)
 | dr_rx_conf_issued => (dr_write_ch0ctrl dr)
 | dr_rx_read_rxs => (NONE, NONE, dr with dr_err := T)
 | dr_rx_check_rxs => (NONE, NONE, dr with dr_err := T)
 | dr_rx_read_rx0 => (NONE, NONE, dr with dr_err := T)
 | dr_rx_fetch_data => (NONE, NONE, dr with dr_err := T)
 | dr_rx_issue_disable => (dr_write_ch0ctrl dr)
 | dr_rx_read_conf => (NONE, NONE, dr with dr_err := T)
 | dr_rx_reset_conf => (dr_write_ch0conf_rx dr)
 | dr_rx_sendback => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_idle => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_fetch_conf => (dr_write_ch0conf_xfer dr)
 | dr_xfer_conf_issued => (dr_write_ch0ctrl dr)
 | dr_xfer_read_txs => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_check_txs => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_write_dataO => (dr_write_tx0 dr)
 | dr_xfer_read_rxs => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_check_rxs => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_read_rx0 => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_fetch_dataI => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_issue_disable => (dr_write_ch0ctrl dr)
 | dr_xfer_read_conf => (NONE, NONE, dr with dr_err := T)
 | dr_xfer_reset_conf => (dr_write_ch0conf_xfer dr)
 | dr_xfer_sendback => (NONE, NONE, dr with dr_err := T)`

(* dr_write_address, dr_write_value, dr_write_value: return specific types. *)
val dr_write_address_def = Define `
dr_write_address (dr:driver_state) =
let (ad, v, dr') = dr_write dr in ad`

val dr_write_value_def = Define `
dr_write_value (dr:driver_state) =
let (ad, v, dr') = dr_write dr in v`

val dr_write_state_def = Define `
dr_write_state (dr:driver_state) =
let (ad, v, dr') = dr_write dr in dr'`

val _ = export_theory();
