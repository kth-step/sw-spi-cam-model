open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "ds_abs1_rel"

(* ds_abs1_spi_tr: ds_abs1 spi internal transtion *)
val (ds_abs1_spi_tr_rules, ds_abs1_spi_tr_ind, ds_abs1_spi_tr_cases) = Hol_reln `
(!(ds_abs1:ds_abs1_state). (SPI_ABS1_TX_ENABLE ds_abs1) ==>
ds_abs1_spi_tr ds_abs1 tau_spi (spi_abs1_tx_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (SPI_ABS1_RX_ENABLE ds_abs1) ==>
ds_abs1_spi_tr ds_abs1 tau_spi (spi_abs1_rx_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (SPI_ABS1_XFER_ENABLE ds_abs1) ==>
ds_abs1_spi_tr ds_abs1 tau_spi (spi_abs1_xfer_operations ds_abs1))`


(* ds_abs1_dr_tr: ds_abs1 driver internal transtion *)
val (ds_abs1_dr_tr_rules, ds_abs1_dr_tr_ind, ds_abs1_dr_tr_cases) = Hol_reln `
(!(ds_abs1:ds_abs1_state). (DRIVER_ABS1_RX_ENABLE ds_abs1) ==>
ds_abs1_dr_tr ds_abs1 tau_dr (driver_abs1_rx_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (DRIVER_ABS1_XFER_ENABLE ds_abs1) ==>
ds_abs1_dr_tr ds_abs1 tau_dr (driver_abs1_xfer_operations ds_abs1))`


(* ds_abs1_comb_tr: ds_abs1 other internal transtion *)
val (ds_abs1_comb_tr_rules, ds_abs1_comb_tr_ind, ds_abs1_comb_tr_cases) = Hol_reln `
(!(ds_abs1:ds_abs1_state). (COMB_ABS1_INIT_ENABLE ds_abs1) ==>
ds_abs1_comb_tr ds_abs1 tau_comb (comb_abs1_init_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (COMB_ABS1_TX_ENABLE ds_abs1) ==>
ds_abs1_comb_tr ds_abs1 tau_comb (comb_abs1_tx_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (COMB_ABS1_RX_ENABLE ds_abs1) ==>
ds_abs1_comb_tr ds_abs1 tau_comb (comb_abs1_rx_operations ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (COMB_ABS1_XFER_ENABLE ds_abs1) ==>
ds_abs1_comb_tr ds_abs1 tau_comb (comb_abs1_xfer_operations ds_abs1))`


(* ds_abs1_tr: the ds_abs1 labeled state transtion *)
val (ds_abs1_tr_rules, ds_abs1_tr_ind, ds_abs1_tr_cases) = Hol_reln `
(* interface for other programs to call the ds_abs1 functions *)
(!(ds_abs1:ds_abs1_state). (ds_abs1.state = abs1_init_pre) \/ (ds_abs1.state = abs1_ready) ==>
ds_abs1_tr ds_abs1 call_init (call_init_ds_abs1 ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (ds_abs1.state = abs1_ready) /\ (buffer <> []) ==>
ds_abs1_tr ds_abs1 (call_tx buffer) (call_tx_ds_abs1 ds_abs1 buffer)) /\
(!(ds_abs1:ds_abs1_state). (ds_abs1.state = abs1_ready) /\ (length > 0) ==>
ds_abs1_tr ds_abs1 (call_rx length) (call_rx_ds_abs1 ds_abs1 length)) /\
(!(ds_abs1:ds_abs1_state). (ds_abs1.state = abs1_ready) /\ (buffer <> []) ==>
ds_abs1_tr ds_abs1 (call_xfer buffer) (call_xfer_ds_abs1 ds_abs1 buffer)) /\
(* tau transition in the model *)
(!(ds_abs1:ds_abs1_state). ds_abs1_spi_tr ds_abs1 tau_spi ds_abs1' ==>
ds_abs1_tr ds_abs1 tau ds_abs1') /\
(!(ds_abs1:ds_abs1_state). ds_abs1_dr_tr ds_abs1 tau_dr ds_abs1' ==>
ds_abs1_tr ds_abs1 tau ds_abs1') /\
(!(ds_abs1:ds_abs1_state). ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1' ==>
ds_abs1_tr ds_abs1 tau ds_abs1') /\
(* cases for the ds_abs1 to transfer data *)
(!(ds_abs1:ds_abs1_state). (ABS1_TX_LBL_ENABLE ds_abs1) ==>
ds_abs1_tr ds_abs1 (TX (abs1_tx_trans_done_op_value ds_abs1)) 
(abs1_tx_trans_done_op_state ds_abs1)) /\
(!(ds_abs1:ds_abs1_state). (ABS1_RX_LBL_ENABLE ds_abs1) /\ (data <> NONE) ==>
ds_abs1_tr ds_abs1 (RX data) (abs1_rx_receive_data_op ds_abs1 data)) /\
(!(ds_abs1:ds_abs1_state). (ds_abs1.state = abs1_xfer_exchange) /\ (dataIN <> NONE) ==>
ds_abs1_tr ds_abs1 (XFER dataIN (abs1_xfer_exchange_op_value ds_abs1 dataIN)) 
(abs1_xfer_exchange_op_state ds_abs1 dataIN))`

(* ds_abs1_tau_only_1_state: tau is the only available transition for the ds_abs1 state. *)
val ds_abs1_tau_only_1_state_def = Define `
ds_abs1_tau_only_1_state (ds_abs1:ds_abs1_state) =
((ds_abs1.state <> abs1_tx_trans) /\
(ds_abs1.state <> abs1_tx_done_2) /\ 
(ds_abs1.state <> abs1_rx_fetch_data) /\
(ds_abs1.state <> abs1_rx_ready) /\
(ds_abs1.state <> abs1_rx_next) /\
(ds_abs1.state <> abs1_xfer_fetch_data))`

val _ = export_theory();
