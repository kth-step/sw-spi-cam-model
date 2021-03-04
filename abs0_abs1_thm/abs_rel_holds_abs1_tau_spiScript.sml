open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory ds_abs0_relTheory abs_relTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_abs1_tau_spi";

(* abs_rel holds for abs1 tx automaton tau_spi transitions *)
val abs_rel_holds_abs1_tau_spi_tx = store_thm("abs_rel_holds_abs1_tau_spi_tx",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (SPI_ABS1_TX_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (spi_abs1_tx_operations ds_abs1))``,
rw [SPI_ABS1_TX_ENABLE_def, spi_abs1_tx_operations_def, spi_abs1_tx_idle_op_def, 
spi_abs1_tx_data_1_op_def, spi_abs1_tx_data_2_op_def, spi_abs1_tx_update_op_def,
spi_abs1_tx_last_update_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def] >>
METIS_TAC []);

(* abs_rel holds for abs1 rx automaton tau_spi transitions *)
val abs_rel_holds_abs1_tau_spi_rx = store_thm("abs_rel_holds_abs1_tau_spi_rx",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (SPI_ABS1_RX_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (spi_abs1_rx_operations ds_abs1))``,
rw [SPI_ABS1_RX_ENABLE_def, spi_abs1_rx_operations_def, spi_abs1_rx_idle_op_def,
spi_abs1_rx_update_op_def, spi_abs1_rx_next_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds for abs1 xfer automaton tau_spi transitions *)
val abs_rel_holds_abs1_tau_spi_xfer = store_thm("abs_rel_holds_abs1_tau_spi_xfer",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (SPI_ABS1_XFER_ENABLE ds_abs1) ==>
(abs_rel ds_abs0 (spi_abs1_xfer_operations ds_abs1))``,
rw [SPI_ABS1_XFER_ENABLE_def, spi_abs1_xfer_operations_def, spi_abs1_xfer_idle_op_def,
spi_abs1_xfer_data_op_def, spi_abs1_xfer_update_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds when ds_abs1 peforms tau_spi *)
val abs_rel_holds_abs1_tau_spi = store_thm("abs_rel_holds_abs1_tau_spi",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (ds_abs1':ds_abs1_state).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1_spi_tr ds_abs1 tau_spi ds_abs1') ==>
(abs_rel ds_abs0 ds_abs1') \/
(?ds_abs0'. ds_abs0_tr ds_abs0 tau ds_abs0' /\ abs_rel ds_abs0' ds_abs1')``,
rw [ds_abs1_spi_tr_cases] >>
rw [abs_rel_holds_abs1_tau_spi_tx, abs_rel_holds_abs1_tau_spi_rx, abs_rel_holds_abs1_tau_spi_xfer]);

val _ = export_theory();
