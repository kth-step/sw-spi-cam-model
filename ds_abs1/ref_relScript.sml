open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open driver_stateTheory;
open ds_abs1_stateTheory;

val _ = new_theory "ref_rel";

(* IS_INIT_REL: ds_abs1_state -> driver_state -> spi_state -> bool *)
val IS_INIT_REL_def = Define `
IS_INIT_REL (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
(((ds_abs1.ds_abs1_init.state = abs1_init_pre) = 
(dr.dr_init.state = dr_init_pre /\ spi.init.state = init_start)) /\
((ds_abs1.ds_abs1_init.state = abs1_init_start) =
((dr.dr_init.state = dr_init_idle /\ spi.init.state = init_start) \/
(dr.dr_init.state = dr_init_read_req /\ spi.init.state = init_reset) \/
(dr.dr_init.state = dr_init_check_rep /\ spi.init.state = init_reset))) /\
((ds_abs1.ds_abs1_init.state = abs1_init_check) =
((dr.dr_init.state = dr_init_read_req /\ spi.init.state = init_setregs) \/
(dr.dr_init.state = dr_init_check_rep /\ spi.init.state = init_setregs))) /\
((ds_abs1.ds_abs1_init.state = abs1_init_done) =
(dr.dr_init.state = dr_init_setting /\ spi.init.state = init_setregs) \/
(dr.dr_init.state = dr_init_done /\ spi.init.state = init_done)))`

(* IS_TX_REL: ds_abs1_state -> driver_state -> spi_state -> bool *)
val IS_TX_REL_def = Define `
IS_TX_REL (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
(((ds_abs1.ds_abs1_tx.state = abs1_tx_pre) =
(dr.dr_tx.state = dr_tx_pre /\ spi.tx.state = tx_idle)) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_idle) =
((dr.dr_tx.state = dr_tx_idle /\ spi.tx.state = tx_idle) \/
(dr.dr_tx.state = dr_tx_conf_issued /\ spi.tx.state = tx_conf_ready) \/
(dr.dr_tx.state = dr_tx_read_txs /\ spi.tx.state = tx_channel_enabled) \/
(dr.dr_tx.state = dr_tx_check_txs /\ spi.tx.state = tx_channel_enabled))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_prepare) =
((dr.dr_tx.state = dr_tx_read_txs /\ spi.tx.state = tx_ready_for_trans) \/
(dr.dr_tx.state = dr_tx_check_txs /\ spi.tx.state = tx_ready_for_trans))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_trans) =
((dr.dr_tx.state = dr_tx_write_data /\ spi.tx.state = tx_ready_for_trans) \/
(dr.dr_tx.state = dr_tx_read_txs /\ spi.tx.state = tx_trans_data) \/
(dr.dr_tx.state = dr_tx_check_txs /\ spi.tx.state = tx_trans_data) \/
(dr.dr_tx.state = dr_tx_read_eot /\ spi.tx.state = tx_trans_data) \/
(dr.dr_tx.state = dr_tx_check_eot /\ spi.tx.state = tx_trans_data))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_done_1) =
((dr.dr_tx.state = dr_tx_read_eot /\ spi.tx.state = tx_trans_done) \/
(dr.dr_tx.state = dr_tx_check_eot /\ spi.tx.state = tx_trans_done))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_done_2) =
((dr.dr_tx.state = dr_tx_read_txs /\ spi.tx.state = tx_trans_done) \/
(dr.dr_tx.state = dr_tx_check_txs /\ spi.tx.state = tx_trans_done))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_done_3) =
(dr.dr_tx.state = dr_tx_write_data /\ spi.tx.state = tx_trans_done)) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_check_1) =
((dr.dr_tx.state = dr_tx_read_eot /\ spi.tx.state = tx_trans_check) \/
(dr.dr_tx.state = dr_tx_check_eot /\ spi.tx.state = tx_trans_check))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_check_2) =
((dr.dr_tx.state = dr_tx_read_eot /\ spi.tx.state = tx_ready_for_trans) \/
(dr.dr_tx.state = dr_tx_check_eot /\ spi.tx.state = tx_ready_for_trans))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_check_3) =
((dr.dr_tx.state = dr_tx_read_txs /\ spi.tx.state = tx_trans_check) \/
(dr.dr_tx.state = dr_tx_check_txs /\ spi.tx.state = tx_trans_check))) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_next) =
(dr.dr_tx.state = dr_tx_write_data /\ spi.tx.state = tx_trans_check)) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_ready_for_reset) =
(dr.dr_tx.state = dr_tx_issue_disable /\ spi.tx.state = tx_trans_check)) /\
((ds_abs1.ds_abs1_tx.state = abs1_tx_reset) =
((dr.dr_tx.state = dr_tx_issue_disable /\ spi.tx.state = tx_ready_for_trans) \/
(dr.dr_tx.state = dr_tx_reset_conf /\ spi.tx.state = tx_channel_disabled))))`

(* IS_RX_REL: ds_abs1_state -> driver_state -> spi_state -> bool *)
val IS_RX_REL_def = Define `
IS_RX_REL (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
(((ds_abs1.ds_abs1_rx.state = abs1_rx_pre) =
(dr.dr_rx.state = dr_rx_pre /\ spi.rx.state = rx_idle)) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_idle) =
((dr.dr_rx.state = dr_rx_idle /\ spi.rx.state = rx_idle) \/
(dr.dr_rx.state = dr_rx_conf_issued /\ spi.rx.state = rx_conf_ready) \/
(dr.dr_rx.state = dr_rx_read_rxs /\ spi.rx.state = rx_channel_enabled) \/
(dr.dr_rx.state = dr_rx_check_rxs /\ spi.rx.state = rx_channel_enabled))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_receive) =
((dr.dr_rx.state = dr_rx_read_rxs /\ spi.rx.state = rx_receive_data) \/
(dr.dr_rx.state = dr_rx_check_rxs /\ spi.rx.state = rx_receive_data))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_update) =
((dr.dr_rx.state = dr_rx_read_rxs /\ spi.rx.state = rx_update_RX0) \/
(dr.dr_rx.state = dr_rx_check_rxs /\ spi.rx.state = rx_update_RX0))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_ready) =
((dr.dr_rx.state = dr_rx_read_rxs /\ spi.rx.state = rx_data_ready) \/
(dr.dr_rx.state = dr_rx_check_rxs /\ spi.rx.state = rx_data_ready))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_fetch_data) =
((dr.dr_rx.state = dr_rx_read_rx0 /\ spi.rx.state = rx_data_ready) /\
(dr.dr_rx.state = dr_rx_fetch_data /\ spi.rx.state = rx_receive_check))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_return) =
((dr.dr_rx.state = dr_rx_read_rxs /\ spi.rx.state = rx_receive_check) \/
(dr.dr_rx.state = dr_rx_check_rxs /\ spi.rx.state = rx_receive_check))) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_done) =
(dr.dr_rx.state = dr_rx_fetch_data /\ spi.rx.state = rx_receive_data)) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_ready_for_reset) =
(dr.dr_rx.state = dr_rx_issue_disable /\ spi.rx.state = rx_receive_check)) /\
((ds_abs1.ds_abs1_rx.state = abs1_rx_reset) =
((dr.dr_rx.state = dr_rx_issue_disable /\ spi.rx.state = rx_receive_data) \/
(dr.dr_rx.state = dr_rx_reset_conf /\ spi.rx.state = rx_channel_disabled))))`

(* IS_XFER_REL: ds_abs1_state -> driver_state -> spi_state -> bool *)
val IS_XFER_REL_def = Define `
IS_XFER_REL (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
(((ds_abs1.ds_abs1_xfer.state = abs1_xfer_pre) =
(dr.dr_xfer.state = dr_xfer_pre /\ spi.xfer.state = xfer_idle)) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_idle) =
((dr.dr_xfer.state = dr_xfer_idle /\ spi.xfer.state = xfer_idle) \/
(dr.dr_xfer.state = dr_xfer_conf_issued /\ spi.xfer.state = xfer_conf_ready) \/
(dr.dr_xfer.state = dr_xfer_read_txs /\ spi.xfer.state = xfer_channel_enabled) \/
(dr.dr_xfer.state = dr_xfer_check_txs /\ spi.xfer.state = xfer_channel_enabled))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_prepare) =
((dr.dr_xfer.state = dr_xfer_read_txs /\ spi.xfer.state = xfer_ready_for_trans) \/
(dr.dr_xfer.state = dr_xfer_check_txs /\ spi.xfer.state = xfer_ready_for_trans))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_trans) =
((dr.dr_xfer.state = dr_xfer_write_dataO /\ spi.xfer.state = xfer_ready_for_trans) \/
(dr.dr_xfer.state = dr_xfer_read_rxs /\ spi.xfer.state = xfer_trans_data) \/
(dr.dr_xfer.state = dr_xfer_check_rxs /\ spi.xfer.state = xfer_trans_data))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_exchange) =
((dr.dr_xfer.state = dr_xfer_read_rxs /\ spi.xfer.state = xfer_exchange_data) \/
(dr.dr_xfer.state = dr_xfer_check_rxs /\ spi.xfer.state = xfer_exchange_data))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_update) =
((dr.dr_xfer.state = dr_xfer_read_rxs /\ spi.xfer.state = xfer_update_RX0) \/
(dr.dr_xfer.state = dr_xfer_check_rxs /\ spi.xfer.state = xfer_update_RX0))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready) =
((dr.dr_xfer.state = dr_xfer_read_rxs /\ spi.xfer.state = xfer_data_ready) \/
(dr.dr_xfer.state = dr_xfer_check_rxs /\ spi.xfer.state = xfer_data_ready))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_fetch_data) =
((dr.dr_xfer.state = dr_xfer_read_rx0 /\ spi.xfer.state = xfer_data_ready) \/
(dr.dr_xfer.state = dr_xfer_fetch_dataI /\ spi.xfer.state = xfer_check))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_next) =
((dr.dr_xfer.state = dr_xfer_read_txs /\ spi.xfer.state = xfer_check) \/
(dr.dr_xfer.state = dr_xfer_check_txs /\ spi.xfer.state = xfer_check))) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_next_write) =
(dr.dr_xfer.state = dr_xfer_write_dataO /\ spi.xfer.state = xfer_check)) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_done) =
(dr.dr_xfer.state = dr_xfer_fetch_dataI /\ spi.xfer.state = xfer_ready_for_trans)) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_ready_for_reset) =
(dr.dr_xfer.state = dr_xfer_issue_disable /\ spi.xfer.state = xfer_check)) /\
((ds_abs1.ds_abs1_xfer.state = abs1_xfer_reset) =
((dr.dr_xfer.state = dr_xfer_issue_disable /\ spi.xfer.state = xfer_ready_for_trans) \/
(dr.dr_xfer.state = dr_xfer_reset_conf /\ spi.xfer.state = xfer_channel_disabled))))`

(* ref_rel: ds_abs1_state -> driver_state -> spi_state -> bool *)
val ref_rel_def = Define `
ref_rel (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
((ds_abs1.err = (dr.dr_err /\ spi.err)) /\
(IS_INIT_REL ds_abs1 dr spi) /\
(IS_TX_REL ds_abs1 dr spi) /\
(IS_RX_REL ds_abs1 dr spi) /\
(IS_XFER_REL ds_abs1 dr spi) /\
(ds_abs1.spi_abs1.TX_SHIFT_REG = spi.TX_SHIFT_REG) /\
(ds_abs1.spi_abs1.RX_SHIFT_REG = spi.RX_SHIFT_REG) /\
(ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.data_buf) /\
(ds_abs1.ds_abs1_rx.rx_data_buffer = dr.dr_rx.rx_data_buf) /\
(ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer = dr.dr_xfer.xfer_dataIN_buf) /\
(ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer = dr.dr_xfer.xfer_dataOUT_buf))`

val _ = export_theory();
