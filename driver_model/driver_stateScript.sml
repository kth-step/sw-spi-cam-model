open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;

(* SPI driver issues memory requests to SPI controller *)
val _ = new_theory "driver_state";

(* driver_state *)
(* dr_init_general_state: spi driver initiliztion fucntion state flags *)
val _ = Datatype `dr_init_general_state =
| dr_init_pre | dr_init_idle | dr_init_read_req 
| dr_init_check_rep | dr_init_setting | dr_init_done`

(* dr_init_state *)
val _ = Datatype `dr_init_state = <|
state: dr_init_general_state;
issue_wr_sysconfig: bool;
issue_wr_modulctrl: bool;
issue_wr_ch0conf_wl: bool;
issue_wr_ch0conf_mode: bool;
issue_wr_ch0conf_speed: bool |>`

(* dr_tx_general_state: spi driver transimit function state flags *)
val _ = Datatype ` dr_tx_general_state =
| dr_tx_not_ready | dr_tx_pre | dr_tx_idle | dr_tx_conf_issued | dr_tx_read_txs 
| dr_tx_check_txs | dr_tx_write_data | dr_tx_read_eot 
| dr_tx_check_eot | dr_tx_issue_disable | dr_tx_reset_conf`

(* dr_tx_state *)
val _ = Datatype `dr_tx_state = <|
state: dr_tx_general_state; 
data_buf: word8 list;
tx_cur_length: num |>`

(* dr_rx_general_state: spi driver receive function state flags *)
val _ = Datatype `dr_rx_general_state = 
| dr_rx_not_ready | dr_rx_pre | dr_rx_idle | dr_rx_conf_issued | dr_rx_read_rxs 
| dr_rx_check_rxs | dr_rx_read_rx0 | dr_rx_fetch_data 
| dr_rx_issue_disable | dr_rx_reset_conf`

(* dr_rx_state *)
val _ = Datatype `dr_rx_state = <|
state: dr_rx_general_state;
rx_data_buf : word8 list;
rx_left_length: num |>`

(* dr_xfer_general_state: spi driver transfer(full-duplex) function state flags *)
val _ = Datatype `dr_xfer_general_state =
| dr_xfer_not_ready | dr_xfer_pre | dr_xfer_idle | dr_xfer_conf_issued 
| dr_xfer_read_txs | dr_xfer_check_txs | dr_xfer_write_dataO 
| dr_xfer_read_rxs | dr_xfer_check_rxs | dr_xfer_read_rx0 
| dr_xfer_fetch_dataI | dr_xfer_issue_disable | dr_xfer_reset_conf`

(* dr_xfer_state *)
val _ = Datatype `dr_xfer_state = <|
state: dr_xfer_general_state;
xfer_dataIN_buf: word8 list;
xfer_dataOUT_buf: word8 list;
xfer_cur_length : num |>`

(* driver_state: spi driver state, including init, tx, rx and xfer functions state *)
val _ = Datatype `driver_state = <|
dr_err: bool;
dr_last_read_ad: word32 option;
dr_last_read_v: word32 option;
dr_init: dr_init_state;
dr_tx: dr_tx_state;
dr_rx: dr_rx_state;
dr_xfer: dr_xfer_state |>`

val _ = export_theory();
