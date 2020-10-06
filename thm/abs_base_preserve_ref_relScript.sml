open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open abs_invTheory ref_RTheory spi_abs_relTheory;
open SPI_initTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;
open SPI_relationTheory SPI_schedulerTheory;

val _ = new_theory "abs_base_preserve_ref_rel";

val abs_ref_rel_base_tau_init = store_thm ("abs_ref_rel_base_tau_init",
``!(spi_abs:spi_abs_state) (spi:spi_state).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(INIT_ENABLE spi) ==>
(refine_R spi_abs (spi_init_operations spi))``,
rw [] >>
`spi.init.state = init_reset` by METIS_TAC[INIT_ENABLE_def] >>
rw [spi_init_operations_def, init_reset_op_def, refine_R_def] >|
[(* registers partial equivalence *)
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
(* eq for err flag and RSR *)
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
(* eq for init state and flags *)
`IS_INIT_REL spi_abs.init spi.init` by METIS_TAC[refine_R_def] >>
`spi_abs.init.state = abs_init_setregs` by METIS_TAC[IS_INIT_REL_def] >>
rw [IS_INIT_REL_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def],
(* eq for tx, rx and xfer states *)
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
(* check Reg SYSSTATUS *)
rw [IS_SYSSTATUS_EQ_def] >>
`IS_INIT_REL spi_abs.init spi.init` by METIS_TAC[refine_R_def] >>
`spi_abs.init.state = abs_init_setregs` by METIS_TAC[IS_INIT_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_init_invariant_def],
(* check Reg CH0STAT.TXS *)
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
(* check Reg CH0STAT.RXS *)
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
(* check Reg CH0STAT.EOT *)
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
(* check Reg RX0 *)
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
(* check TX_SHIFT_REG (TSR) *)
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]]);

val abs_ref_rel_base_tau_tx = store_thm ("abs_ref_rel_base_tau_tx",
``!(spi_abs:spi_abs_state) (spi:spi_state).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(TX_ENABLE spi) ==>
(refine_R spi_abs (spi_tx_operations spi))``,
rw [spi_tx_operations_def] >>
Cases_on `spi.tx.state` >|
[(* tx_idle, tx_conf_ready:no tau transition *)
METIS_TAC [TX_ENABLE_def],
METIS_TAC [TX_ENABLE_def],
(* tx_channel_enabled *)
rw [tx_channel_enabled_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_ready_for_trans` by METIS_TAC[IS_TX_REL_def] >>
rw [IS_TX_REL_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_ready_for_trans` by METIS_TAC[IS_TX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_tx_invariant_def] >>
rw [IS_TXS_EQ_def],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* tx_ready_for_trans: no tau transition *)
METIS_TAC [TX_ENABLE_def],
(* tx_trans_data *)
rw [tx_trans_data_op_def, refine_R_def] >| [
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_trans_done` by METIS_TAC[IS_TX_REL_def] >>
rw [IS_TX_REL_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_trans_done` by METIS_TAC[IS_TX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_tx_invariant_def] >>
rw [IS_TXS_EQ_def],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_trans_done` by METIS_TAC[IS_TX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_tx_invariant_def] >>
rw [IS_EOT_EQ_def],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_trans_done` by METIS_TAC[IS_TX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_tx_invariant_def] >>
rw [IS_TSR_EQ_def] >>
`spi_abs.regs.TX0 = spi.regs.TX0` by METIS_TAC[refine_R_def, spi_regs_part_eq_def] >>
rw []],
(* tx_trans_done: no tau transition *)
METIS_TAC [TX_ENABLE_def],
(* tx_trans_check *)
rw [tx_trans_check_op_def] >>
rw [refine_R_def] >| [
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_TX_REL spi_abs.tx spi.tx` by METIS_TAC[refine_R_def] >>
`spi_abs.tx.state = abs_tx_ready_for_trans` by METIS_TAC[IS_TX_REL_def] >>
rw [IS_TX_REL_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* tx_channel_disabled: no tau transition *)
METIS_TAC [TX_ENABLE_def]]);

val abs_ref_rel_base_tau_rx = store_thm("abs_ref_rel_base_tau_rx",
``!(spi_abs:spi_abs_state) (spi:spi_state).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(RX_ENABLE spi) ==> 
(refine_R spi_abs (spi_rx_operations spi))``,
rw [spi_rx_operations_def] >>
Cases_on `spi.rx.state` >| [
(* rx_idle, rx_conf_ready:no tau transition *)
METIS_TAC[RX_ENABLE_def],
METIS_TAC[RX_ENABLE_def],
(* rx_channel_enabled *)
rw [rx_channel_enabled_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_receive_data` by METIS_TAC[IS_RX_REL_def] >>
rw [IS_RX_REL_def],
METIS_TAC [refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_receive_data` by METIS_TAC[IS_RX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_rx_invariant_def] >>
rw [IS_RXS_EQ_def],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* rx_receive_data: no tau transition *)
METIS_TAC [RX_ENABLE_def],
(* rx_update_RX0 *)
rw [rx_update_RX0_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_data_ready` by METIS_TAC[IS_RX_REL_def] >>
rw [IS_RX_REL_def],
METIS_TAC [refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_data_ready` by METIS_TAC[IS_RX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_rx_invariant_def] >>
rw [IS_RXS_EQ_def],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_data_ready` by METIS_TAC[IS_RX_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_rx_invariant_def] >>
rw [IS_RX0_EQ_def] >>
METIS_TAC[refine_R_def],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* rx_data_ready: no tau transition *)
METIS_TAC [RX_ENABLE_def],
(* rx_receive_check *)
rw [rx_receive_check_op_def] >>
rw [refine_R_def] >|[
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_RX_REL spi_abs.rx spi.rx` by METIS_TAC[refine_R_def] >>
`spi_abs.rx.state = abs_rx_receive_data` by METIS_TAC[IS_RX_REL_def] >>
rw [IS_RX_REL_def],
METIS_TAC [refine_R_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* rx_channel_disabled: no tau transition *)
METIS_TAC [RX_ENABLE_def]]);

val abs_ref_rel_base_tau_xfer = store_thm("abs_ref_rel_base_tau_xfer",
``!(spi_abs:spi_abs_state) (spi:spi_state).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(XFER_ENABLE spi) ==> 
(refine_R spi_abs (spi_xfer_operations spi))``,
rw [spi_xfer_operations_def] >>
Cases_on `spi.xfer.state` >|
[(* xfer_idle, xfer_conf_ready: no tau transition *)
METIS_TAC [XFER_ENABLE_def],
METIS_TAC [XFER_ENABLE_def],
(* xfer_channel_enabled *)
rw [xfer_channel_enabled_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_ready_for_trans` by METIS_TAC[IS_XFER_REL_def] >>
rw [IS_XFER_REL_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_ready_for_trans` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_xfer_invariant_def] >>
rw [IS_TXS_EQ_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_ready_for_trans` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_xfer_invariant_def] >>
rw [IS_RXS_EQ_def],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* xfer_ready_for_trans: no tau transition *)
METIS_TAC[XFER_ENABLE_def],
(* xfer_trans_data *)
rw [xfer_trans_data_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_exchange_data` by METIS_TAC[IS_XFER_REL_def] >>
rw [IS_XFER_REL_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC [],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_exchange_data` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def, spi_abs_xfer_invariant_def] >>
rw [IS_TXS_EQ_def],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC [],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_exchange_data` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def, spi_abs_xfer_invariant_def] >>
rw [IS_EOT_EQ_def],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_exchange_data` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def,spi_abs_xfer_invariant_def] >>
rw [IS_TSR_EQ_def] >>
`spi_abs.regs.TX0 = spi.regs.TX0` by METIS_TAC[refine_R_def, spi_regs_part_eq_def] >>
rw []],
(* xfer_exchange_data: no tau transition *)
METIS_TAC[XFER_ENABLE_def],
(* xfer_update_RX0 *)
rw [xfer_update_RX0_op_def, refine_R_def] >|[
`spi_regs_part_eq spi_abs.regs spi.regs` by METIS_TAC [refine_R_def] >> 
rw [spi_regs_part_eq_def] >>
FULL_SIMP_TAC std_ss [spi_regs_part_eq_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
METIS_TAC[refine_R_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_data_ready` by METIS_TAC[IS_XFER_REL_def] >>
rw [IS_XFER_REL_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC [],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC [],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_data_ready` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def, spi_abs_xfer_invariant_def] >>
rw [IS_RXS_EQ_def],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC [],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_data_ready` by METIS_TAC[IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [spi_abs_invariant_def, spi_abs_xfer_invariant_def] >>
rw [IS_RX0_EQ_def] >>
METIS_TAC[refine_R_def, spi_regs_part_eq_def],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC []],
(* xfer_data_ready: no tau transition *)
METIS_TAC [XFER_ENABLE_def],
(* xfer_check *)
rw [xfer_check_op_def] >>
rw [refine_R_def] >| [
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
METIS_TAC [refine_R_def],
`IS_XFER_REL spi_abs.xfer spi.xfer` by METIS_TAC[refine_R_def] >>
`spi_abs.xfer.state = abs_xfer_ready_for_trans` by METIS_TAC[IS_XFER_REL_def] >>
rw [IS_XFER_REL_def],
`IS_SYSSTATUS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_SYSSTATUS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_SYSSTATUS_EQ_def] >>
METIS_TAC[],
`IS_TXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TXS_EQ_def] >>
METIS_TAC[],
`IS_RXS_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RXS_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RXS_EQ_def] >>
METIS_TAC[],
`IS_EOT_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_EOT_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_EOT_EQ_def] >>
METIS_TAC[],
`IS_RX0_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_RX0_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_RX0_EQ_def] >>
METIS_TAC[],
`IS_TSR_EQ spi_abs spi` by METIS_TAC[refine_R_def] >>
rw [IS_TSR_EQ_def] >>
FULL_SIMP_TAC std_ss [IS_TSR_EQ_def] >>
METIS_TAC[]],
(* xfer_channel_disabled *)
METIS_TAC [XFER_ENABLE_def]]);

val abs_ref_rel_base_tau = store_thm("abs_ref_rel_base_tau",
``!(spi_abs:spi_abs_state) (spi:spi_state).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(spi_tr spi tau spi') ==> (refine_R spi_abs spi')``,
rw [spi_tr_cases] >>
rw [abs_ref_rel_base_tau_init, abs_ref_rel_base_tau_tx, 
abs_ref_rel_base_tau_rx, abs_ref_rel_base_tau_xfer]);

val abs_ref_rel_base_TX = store_thm("abs_ref_rel_base_TX",
``!(spi_abs:spi_abs_state) (spi:spi_state) (d:word8 option).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(spi_tr spi (TX d) spi') ==> 
?spi_abs'. (spi_abs_tr spi_abs (TX d) spi_abs') /\ (refine_R spi_abs' spi')``,
cheat);

val abs_ref_rel_base_RX = store_thm("abs_ref_rel_base_RX",
``!(spi_abs:spi_abs_state) (spi:spi_state) (d:word8 option).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(spi_tr spi (RX d) spi') ==> 
?spi_abs'. (spi_abs_tr spi_abs (RX d) spi_abs') /\ (refine_R spi_abs' spi')``,
cheat);

val abs_ref_rel_base_XFER = store_thm("abs_ref_rel_base_XFER",
``!(spi_abs:spi_abs_state) (spi:spi_state) (d0:word8 option) (d1:word8 option).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(spi_tr spi (XFER d0 d1) spi') ==> 
?spi_abs'. (spi_abs_tr spi_abs (XFER d0 d1) spi_abs') /\ (refine_R spi_abs' spi')``,
cheat);

val abs_base_preserve_refinement_relation = 
store_thm("abs_base_preserve_refinement_relation",
``!(spi_abs:spi_abs_state) (spi:spi_state) (l:global_lbl_type).
(spi_abs_invariant spi_abs) /\ (refine_R spi_abs spi) /\
(spi_tr spi l spi') ==> 
(l = tau ==> (refine_R spi_abs spi')) /\
(l <> tau ==> ?spi_abs'.(spi_abs_tr spi_abs l spi_abs') /\ (refine_R spi_abs' spi'))``,
rw [] >|
[(* l = tau *)
METIS_TAC [abs_ref_rel_base_tau],
(* l <> tau *)
Cases_on `l` >|
[ (* ~(tau <> tau) *)
rw [],
METIS_TAC [abs_ref_rel_base_TX],
METIS_TAC [abs_ref_rel_base_RX],
METIS_TAC [abs_ref_rel_base_XFER],
write,
METIS_TAC [abs_ref_rel_base_Update]
read,
METIS_TAC [abs_ref_rel_base_Return]]);


val _ = export_theory();
