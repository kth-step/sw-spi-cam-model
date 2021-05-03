open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;

val _ = new_theory "driver_state";

(* dr_general_state: spi driver general states *)
val _ = Datatype `dr_general_state =
| dr_init_pre | dr_init_idle | dr_init_read_req 
| dr_init_check_rep | dr_init_setting | dr_ready
| dr_tx_idle | dr_tx_fetch_conf | dr_tx_conf_issued 
| dr_tx_read_txs | dr_tx_check_txs | dr_tx_write_data 
| dr_tx_read_eot | dr_tx_check_eot | dr_tx_issue_disable 
| dr_tx_read_conf | dr_tx_reset_conf
| dr_rx_idle | dr_rx_fetch_conf | dr_rx_conf_issued 
| dr_rx_read_rxs | dr_rx_check_rxs | dr_rx_read_rx0 | dr_rx_fetch_data 
| dr_rx_issue_disable | dr_rx_read_conf | dr_rx_reset_conf | dr_rx_sendback
| dr_xfer_idle | dr_xfer_fetch_conf | dr_xfer_conf_issued | dr_xfer_read_txs 
| dr_xfer_check_txs | dr_xfer_write_dataO | dr_xfer_read_rxs 
| dr_xfer_check_rxs | dr_xfer_read_rx0 | dr_xfer_fetch_dataI 
| dr_xfer_issue_disable | dr_xfer_read_conf | dr_xfer_reset_conf | dr_xfer_sendback`

(* dr_init_state: contains boolean flags to record init process *)
val _ = Datatype `dr_init_state = <|
issue_wr_sysconfig: bool;
issue_wr_modulctrl: bool |>`

(* dr_tx_state: include the transimit buffer and a pointer *)
val _ = Datatype `dr_tx_state = <|
tx_data_buf: word8 list;
tx_cur_length: num |>`

(* dr_rx_state: include the receive buffer and a pointer *)
val _ = Datatype `dr_rx_state = <|
rx_data_buf : word8 list;
rx_left_length: num |>`

(* dr_xfer_state: include the two data buffers for transmitting and receiving, and a pointer *)
val _ = Datatype `dr_xfer_state = <|
xfer_dataIN_buf: word8 list;
xfer_dataOUT_buf: word8 list;
xfer_cur_length : num |>`

(* driver_state: include an error flag, general state, reocrds for the last read operation, and init, tx, rx, xfer states.*)
val _ = Datatype `driver_state = <|
dr_err: bool;
state: dr_general_state;
dr_last_read_ad: word32 option;
dr_last_read_v: word32 option;
dr_init: dr_init_state;
dr_tx: dr_tx_state;
dr_rx: dr_rx_state;
dr_xfer: dr_xfer_state |>`

val _ = export_theory();
