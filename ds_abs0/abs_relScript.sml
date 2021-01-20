open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory;
open ds_abs1_stateTheory;

val _ = new_theory "abs_rel"

(* IS_ABS_STATE_REL: ds_abs0_state -> ds_abs1_state -> bool *)
val IS_ABS_STATE_REL_def = Define `
IS_ABS_STATE_REL (ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) =
(((ds_abs0.state = abs0_init) =
(ds_abs1.state = abs1_init_pre)) /\
((ds_abs0.state = abs0_ready) =
((ds_abs1.state = abs1_init_start) \/
(ds_abs1.state = abs1_ready) \/
(ds_abs1.state = abs1_tx_reset) \/
(ds_abs1.state = abs1_rx_reset) \/
(ds_abs1.state = abs1_xfer_reset))) /\
((ds_abs0.state = abs0_tx) =
((ds_abs1.state = abs1_tx_idle) \/
(ds_abs1.state = abs1_tx_trans) \/
(ds_abs1.state = abs1_tx_data_1) \/
(ds_abs1.state = abs1_tx_data_2) \/
(ds_abs1.state = abs1_tx_done_1) \/
(ds_abs1.state = abs1_tx_done_2) \/
(ds_abs1.state = abs1_tx_next) \/
(ds_abs1.state = abs1_tx_update) \/
(ds_abs1.state = abs1_tx_last) \/
(ds_abs1.state = abs1_tx_last_update))) /\
((ds_abs0.state = abs0_rx_idle) =
((ds_abs1.state = abs1_rx_idle) \/
(ds_abs1.state = abs1_rx_receive))) /\
((ds_abs0.state = abs0_rx_update) =
((ds_abs1.state = abs1_rx_update) \/
(ds_abs1.state = abs1_rx_ready))) /\
((ds_abs0.state = abs0_rx_reading) =
((ds_abs1.state = abs1_rx_read) \/
(ds_abs1.state = abs1_rx_fetch_data))) /\
((ds_abs0.state = abs0_rx_next) =
((ds_abs1.state = abs1_rx_next) \/
(ds_abs1.state = abs1_rx_next_ready))) /\
((ds_abs0.state = abs0_xfer_idle) =
((ds_abs1.state = abs1_xfer_idle) \/
(ds_abs1.state = abs1_xfer_prepare) \/
(ds_abs1.state = abs1_xfer_data) \/
(ds_abs1.state = abs1_xfer_exchange))) /\
((ds_abs0.state = abs0_xfer_done) =
((ds_abs1.state = abs1_xfer_update) \/
(ds_abs1.state = abs1_xfer_ready) \/
(ds_abs1.state = abs1_xfer_fetch_data))))`

(* abs_rel: ds_abs0_state -> ds_abs1_state -> bool *)
val abs_rel_def = Define `
abs_rel (ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) =
((ds_abs0.err = ds_abs1.err) /\
(IS_ABS_STATE_REL ds_abs0 ds_abs1) /\
(ds_abs0.ds_abs0_tx.tx_data_buffer = ds_abs1.ds_abs1_tx.tx_data_buffer) /\
(ds_abs0.ds_abs0_tx.tx_cur_length = ds_abs1.ds_abs1_tx.tx_cur_length) /\
(ds_abs0.ds_abs0_rx.rx_data_buffer = ds_abs1.ds_abs1_rx.rx_data_buffer) /\
(ds_abs0.ds_abs0_rx.rx_left_length = ds_abs1.ds_abs1_rx.rx_left_length) /\
(ds_abs0.ds_abs0_xfer.xfer_dataIN_buffer = ds_abs1.ds_abs1_xfer.xfer_dataIN_buffer) /\
(ds_abs0.ds_abs0_xfer.xfer_dataOUT_buffer = ds_abs1.ds_abs1_xfer.xfer_dataOUT_buffer) /\
(ds_abs0.ds_abs0_xfer.xfer_cur_length = ds_abs1.ds_abs1_xfer.xfer_cur_length) /\
(* some requirements for rx automaton *)
(ds_abs0.state = abs0_rx_reading ==> ds_abs1.spi_abs1.RX_SHIFT_REG = ds_abs0.ds_abs0_rx.temp_RSR) /\
(ds_abs0.state = abs0_rx_update ==> ds_abs1.spi_abs1.RX_SHIFT_REG = ds_abs0.ds_abs0_rx.temp_RSR) /\
(ds_abs0.state = abs0_rx_next ==> ds_abs1.spi_abs1.RX_SHIFT_REG = ds_abs0.ds_abs0_rx.temp_RSR) /\
(ds_abs0.state = abs0_rx_next ==> ds_abs1.ds_abs1_rx.temp_value = ds_abs0.ds_abs0_rx.temp_value) /\
(ds_abs0.state = abs0_xfer_done ==> ds_abs1.spi_abs1.RX_SHIFT_REG = ds_abs0.ds_abs0_xfer.xfer_RSR))`

val _ = export_theory();
