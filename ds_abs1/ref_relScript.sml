open HolKernel bossLib boolLib Parse;
open wordsTheory listTheory;
open SPI_stateTheory;
open driver_stateTheory;
open ds_abs1_stateTheory;
open board_memTheory;

val _ = new_theory "ref_rel";

(* IS_STATE_REL: ds_abs1_state -> driver_state -> spi_state -> bool *)
val IS_STATE_REL_def = Define `
IS_STATE_REL (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
(((ds_abs1.state = abs1_init_pre) = 
(dr.state = dr_init_pre /\ spi.state = init_start)) /\
((ds_abs1.state = abs1_init_start) =
((dr.state = dr_init_idle /\ spi.state = init_start) \/
(dr.state = dr_init_read_req /\ spi.state = init_reset) \/
(dr.state = dr_init_check_rep /\ spi.state = init_reset) \/
(dr.state = dr_init_read_req /\ spi.state = init_setregs) \/
(dr.state = dr_init_check_rep /\ spi.state = init_setregs) \/
(dr.state = dr_init_setting /\ spi.state = init_setregs) \/
(dr.state = dr_init_idle /\ spi.state = spi_ready))) /\
((ds_abs1.state = abs1_ready) =
(dr.state = dr_ready /\ spi.state = spi_ready)) /\
((ds_abs1.state = abs1_tx_idle) =
((dr.state = dr_tx_idle /\ spi.state = spi_ready) \/
(dr.state = dr_tx_conf_issued /\ spi.state = tx_conf_ready) \/
(dr.state = dr_tx_read_txs /\ spi.state = tx_channel_enabled) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_channel_enabled))) /\
((ds_abs1.state = abs1_tx_trans) =
((dr.state = dr_tx_read_txs /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_write_data /\ spi.state = tx_ready_for_trans))) /\
((ds_abs1.state = abs1_tx_data_1) =
((dr.state = dr_tx_read_eot /\ spi.state = tx_trans_data) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_trans_data))) /\
((ds_abs1.state = abs1_tx_data_2) =
((dr.state = dr_tx_read_txs /\ spi.state = tx_trans_data) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_data))) /\
((ds_abs1.state = abs1_tx_done_1) =
((dr.state = dr_tx_read_eot /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_trans_done))) /\
((ds_abs1.state = abs1_tx_done_2) =
((dr.state = dr_tx_read_txs /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_write_data /\ spi.state = tx_trans_done))) /\
((ds_abs1.state = abs1_tx_reset) =
((dr.state = dr_tx_read_eot /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_issue_disable /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_reset_conf /\ spi.state = tx_channel_disabled))) /\
((ds_abs1.state = abs1_rx_idle) =
((dr.state = dr_rx_idle /\ spi.state = spi_ready) \/
(dr.state = dr_rx_conf_issued /\ spi.state = rx_conf_ready) \/
(dr.state = dr_rx_read_rxs /\ spi.state = rx_channel_enabled) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_channel_enabled))) /\
((ds_abs1.state = abs1_rx_receive) =
((dr.state = dr_rx_read_rxs /\ spi.state = rx_receive_data) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_receive_data))) /\
((ds_abs1.state = abs1_rx_update) =
((dr.state = dr_rx_read_rxs /\ spi.state = rx_update_RX0) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_update_RX0))) /\
((ds_abs1.state = abs1_rx_ready) =
((dr.state = dr_rx_read_rxs /\ spi.state = rx_data_ready) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_data_ready) \/
(dr.state = dr_rx_read_rx0 /\ spi.state = rx_data_ready))) /\
((ds_abs1.state = abs1_rx_fetch_data) =
(dr.state = dr_rx_fetch_data /\ spi.state = rx_receive_data)) /\
((ds_abs1.state = abs1_rx_done) =
(dr.state = dr_rx_issue_disable /\ spi.state = rx_receive_data)) /\
((ds_abs1.state = abs1_rx_stop) = 
(dr.state = dr_rx_issue_disable /\ spi.state = rx_update_RX0)) /\
((ds_abs1.state = abs1_rx_next) = 
(dr.state = dr_rx_fetch_data /\ spi.state = rx_update_RX0)) /\
((ds_abs1.state = abs1_rx_next_ready) = 
(dr.state = dr_rx_fetch_data /\ spi.state = rx_data_ready)) /\
((ds_abs1.state = abs1_rx_reset) =
((dr.state = dr_rx_issue_disable /\ spi.state = rx_data_ready) \/
(dr.state = dr_rx_reset_conf /\ spi.state = rx_channel_disabled))) /\
((ds_abs1.state = abs1_xfer_idle) =
((dr.state = dr_xfer_idle /\ spi.state = spi_ready) \/
(dr.state = dr_xfer_conf_issued /\ spi.state = xfer_conf_ready) \/
(dr.state = dr_xfer_read_txs /\ spi.state = xfer_channel_enabled) \/
(dr.state = dr_xfer_check_txs /\ spi.state = xfer_channel_enabled))) /\
((ds_abs1.state = abs1_xfer_prepare) =
((dr.state = dr_xfer_read_txs /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_check_txs /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_write_dataO /\ spi.state = xfer_ready_for_trans))) /\
((ds_abs1.state = abs1_xfer_data) =
((dr.state = dr_xfer_read_rxs /\ spi.state = xfer_trans_data) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_trans_data))) /\
((ds_abs1.state = abs1_xfer_exchange) =
((dr.state = dr_xfer_read_rxs /\ spi.state = xfer_exchange_data) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_exchange_data))) /\
((ds_abs1.state = abs1_xfer_update) =
((dr.state = dr_xfer_read_rxs /\ spi.state = xfer_update_RX0) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_update_RX0))) /\
((ds_abs1.state = abs1_xfer_ready) =
((dr.state = dr_xfer_read_rxs /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_read_rx0 /\ spi.state = xfer_data_ready))) /\
((ds_abs1.state = abs1_xfer_fetch_data) =
(dr.state = dr_xfer_fetch_dataI /\ spi.state = xfer_ready_for_trans)) /\
((ds_abs1.state = abs1_xfer_reset) =
((dr.state = dr_xfer_issue_disable /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_reset_conf /\ spi.state = xfer_channel_disabled))))`

(* ref_rel: ds_abs1_state -> driver_state -> spi_state -> bool *)
val ref_rel_def = Define `
ref_rel (ds_abs1:ds_abs1_state) (dr:driver_state) (spi:spi_state) =
((* err flag *)
(ds_abs1.err = (dr.dr_err \/ spi.err)) /\
(* states of the abstract and concrete models are related *)
(IS_STATE_REL ds_abs1 dr spi) /\
(* shift registers *)
(ds_abs1.spi_abs1.TX_SHIFT_REG = spi.TX_SHIFT_REG) /\
(ds_abs1.spi_abs1.RX_SHIFT_REG = spi.RX_SHIFT_REG) /\
(* data buffer and length indicator for tx, rx and xfer *)
(ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.tx_data_buf) /\
(ds_abs1.ds_abs1_tx.tx_cur_length = dr.dr_tx.tx_cur_length) /\
(ds_abs1.ds_abs1_rx.rx_data_buffer = dr.dr_rx.rx_data_buf) /\
(ds_abs1.ds_abs1_rx.rx_left_length = dr.dr_rx.rx_left_length) /\
(ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer = dr.dr_xfer.xfer_dataIN_buf) /\
(ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer = dr.dr_xfer.xfer_dataOUT_buf) /\
(ds_abs1.ds_abs1_xfer.xfer_cur_length = dr.dr_xfer.xfer_cur_length) /\
(* rules for simulation proof, spi tau part *)
(spi.state = tx_trans_data ==> 
(w2w spi.regs.TX0 = EL (dr.dr_tx.tx_cur_length - 1) dr.dr_tx.tx_data_buf)) /\
(spi.state = xfer_trans_data ==>
(w2w spi.regs.TX0 = EL (dr.dr_xfer.xfer_cur_length - 1) dr.dr_xfer.xfer_dataOUT_buf)) /\
(* rules for simulation proof, dr tau part *)
(dr.state = dr_init_check_rep ==> dr.dr_last_read_ad = SOME SPI0_SYSSTATUS) /\
(dr.state = dr_tx_check_txs ==> dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.state = dr_tx_check_eot ==> dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.state = dr_rx_check_rxs ==> dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.state = dr_rx_fetch_data ==> dr.dr_last_read_ad = SOME SPI0_RX0) /\
(dr.state = dr_xfer_check_txs ==> dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.state = dr_xfer_check_rxs ==> dr.dr_last_read_ad = SOME SPI0_CH0STAT) /\
(dr.state = dr_xfer_fetch_dataI ==> dr.dr_last_read_ad = SOME SPI0_RX0) /\
(* for init automaton *)
(spi.state = init_reset /\ dr.state = dr_init_check_rep ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = init_reset ==> spi.regs.SYSSTATUS = 0w) /\
(* for tx automaton *)
(spi.state = tx_channel_enabled /\ dr.state = dr_tx_check_txs ==>
(1 >< 1) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = tx_trans_data /\ dr.state = dr_tx_check_txs ==>
(1 >< 1) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = tx_trans_data /\ dr.state = dr_tx_check_eot ==>
(2 >< 2) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = tx_trans_done /\ dr.state = dr_tx_check_eot ==>
(2 >< 2) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = tx_channel_enabled ==> spi.regs.CH0STAT.TXS = 0w) /\
(spi.state = tx_trans_data ==> spi.regs.CH0STAT.TXS = 0w /\ spi.regs.CH0STAT.EOT = 0w) /\
(spi.state = tx_trans_done ==> spi.regs.CH0STAT.EOT = 0w) /\
(* for rx automaton *)
(spi.state = rx_channel_enabled /\ dr.state = dr_rx_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = rx_receive_data /\ dr.state = dr_rx_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = rx_update_RX0 /\ dr.state = dr_rx_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = rx_receive_data /\ dr.state = dr_rx_fetch_data ==>
spi.RX_SHIFT_REG = (7 >< 0) (THE dr.dr_last_read_v):word8) /\
(spi.state = rx_update_RX0 /\ dr.state = dr_rx_fetch_data ==>
ds_abs1.ds_abs1_rx.temp_value = (7 >< 0) (THE dr.dr_last_read_v):word8) /\
(spi.state = rx_receive_data /\ dr.state = dr_rx_fetch_data ==>
ds_abs1.ds_abs1_rx.temp_value = (7 >< 0) (THE dr.dr_last_read_v):word8) /\
(spi.state = rx_data_ready /\ dr.state = dr_rx_fetch_data ==>
ds_abs1.ds_abs1_rx.temp_value = (7 >< 0) (THE dr.dr_last_read_v):word8) /\
(spi.state = rx_channel_enabled ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = rx_receive_data ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = rx_update_RX0 ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = rx_data_ready ==> spi.RX_SHIFT_REG = (7 >< 0) spi.regs.RX0 /\
spi.regs.CH0STAT.RXS = 1w) /\
(* for xfer automaton *)
(spi.state = xfer_channel_enabled /\ dr.state = dr_xfer_check_txs ==>
(1 >< 1) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = xfer_trans_data /\ dr.state = dr_xfer_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = xfer_exchange_data /\ dr.state = dr_xfer_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = xfer_update_RX0 /\ dr.state = dr_xfer_check_rxs ==>
(0 >< 0) (THE dr.dr_last_read_v) = 0w:word1) /\
(spi.state = xfer_ready_for_trans /\ dr.state = dr_xfer_fetch_dataI ==>
spi.RX_SHIFT_REG = (7 >< 0) (THE dr.dr_last_read_v):word8) /\
(spi.state = xfer_channel_enabled ==> spi.regs.CH0STAT.TXS = 0w /\ spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = xfer_ready_for_trans ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = xfer_trans_data ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = xfer_exchange_data ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = xfer_update_RX0 ==> spi.regs.CH0STAT.RXS = 0w) /\
(spi.state = xfer_data_ready ==> spi.RX_SHIFT_REG = (7 >< 0) spi.regs.RX0 /\
spi.regs.CH0STAT.RXS = 1w))`


val _ = export_theory();