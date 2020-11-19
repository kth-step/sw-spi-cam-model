open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory SPI_initTheory SPI_txTheory SPI_rxTheory
SPI_xferTheory SPI_schedulerTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;


val _ = new_theory "abs1_comb_hold_ref_rel_spi_tr";

(* a lemma: INIT_ENABLE => SPI_ABS1_INIT_ENABLE based on ref_rel *)
val COMB_IMP_ABS1_INIT_ENABLE = store_thm("COMB_IMP_ABS1_INIT_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (INIT_ENABLE spi) ==>
(SPI_ABS1_INIT_ENABLE ds_abs1)``,
rw [INIT_ENABLE_def, SPI_ABS1_INIT_ENABLE_def] >>
`IS_INIT_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >> 
FULL_SIMP_TAC std_ss [IS_INIT_REL_def] >>
rw [] >|
[Cases_on `dr.dr_init.state` >>
rw [] >|
[`spi.init.state <> init_start` by rw [] >>
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw [],
`spi.init.state <> init_start` by rw [] >>
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw [],
`spi.init.state <> init_setregs` by rw [] >>
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw [],
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw []],
Cases_on `spi.init.state` >>
rw []]);

(* ds_abs1' exists when spi performs init tau transition *)
val ref_rel_spi_init_tau = store_thm("ref_rel_spi_init_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (INIT_ENABLE spi) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' dr (spi_init_operations spi))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_init_operations ds_abs1`` >>
`SPI_ABS1_INIT_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_INIT_ENABLE] >>
rw [] >>
FULL_SIMP_TAC std_ss [INIT_ENABLE_def, SPI_ABS1_INIT_ENABLE_def] >>
rw [spi_abs1_init_operations_def, spi_abs1_init_start_op_def,
spi_init_operations_def, init_reset_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []);

(* a lemma: TX_ENABLE => SPI_ABS1_TX_ENABLE based on ref_rel *)
val COMB_IMP_ABS1_TX_ENABLE = store_thm("COMB_IMP_ABS1_TX_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (TX_ENABLE spi) ==>
(SPI_ABS1_TX_ENABLE ds_abs1)``,
rw [TX_ENABLE_def, SPI_ABS1_TX_ENABLE_def] >>
`IS_TX_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
Cases_on `spi.tx.state` >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def] >>
rw [] >>
Cases_on `dr.dr_tx.state` >>
rw [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw []);

val ref_rel_spi_tx_tau = store_thm("ref_rel_spi_tx_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (TX_ENABLE spi) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' dr (spi_tx_operations spi))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_tx_operations ds_abs1`` >>
`SPI_ABS1_TX_ENABLE ds_abs1` by METIS_TAC[COMB_IMP_ABS1_TX_ENABLE] >>
rw [] >>
FULL_SIMP_TAC std_ss [TX_ENABLE_def, SPI_ABS1_TX_ENABLE_def] >|
[(* abs1_tx_idle *)
`spi.tx.state = tx_channel_enabled` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_idle_op_def,
spi_tx_operations_def, tx_channel_enabled_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_tx_trans_data *)
`spi.tx.state = tx_trans_data` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_trans_op_def,
spi_tx_operations_def, tx_trans_data_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
cheat,
(* abs1_tx_check_1 *)
`spi.tx.state = tx_trans_check` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_check_1_op_def,
spi_tx_operations_def, tx_trans_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_tx_check_3 *)
`spi.tx.state = tx_trans_check` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_check_3_op_def,
spi_tx_operations_def, tx_trans_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_tx_next *)
`spi.tx.state = tx_trans_check` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_next_op_def,
spi_tx_operations_def, tx_trans_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_tx_ready_for_reset *)
`spi.tx.state = tx_trans_check` by METIS_TAC [ref_rel_def, IS_TX_REL_def] >>
rw [spi_abs1_tx_operations_def, spi_abs1_tx_ready_for_reset_op_def,
spi_tx_operations_def, tx_trans_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a lemma: RX_ENABLE => SPI_ABS1_RX_ENABLE based on ref_rel *)
val COMB_IMP_ABS1_RX_ENABLE = store_thm("COMB_IMP_ABS1_RX_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (RX_ENABLE spi) ==>
(SPI_ABS1_RX_ENABLE ds_abs1)``,
rw [RX_ENABLE_def, SPI_ABS1_RX_ENABLE_def] >>
`IS_RX_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
Cases_on `spi.rx.state` >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_RX_REL_def] >>
rw [] >>
Cases_on `dr.dr_rx.state` >>
rw [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw []);

(* ds_abs1' exists when spi performs rx tau transition *)
val ref_rel_spi_rx_tau = store_thm("ref_rel_spi_rx_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (RX_ENABLE spi) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' dr (spi_rx_operations spi))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_rx_operations ds_abs1`` >>
`SPI_ABS1_RX_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_RX_ENABLE] >>
rw [] >>
FULL_SIMP_TAC std_ss [RX_ENABLE_def, SPI_ABS1_RX_ENABLE_def] >|
[(* abs1_rx_idle *)
`spi.rx.state = rx_channel_enabled` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_idle_op_def,
spi_rx_operations_def, rx_channel_enabled_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_update *)
`spi.rx.state = rx_update_RX0` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_update_op_def,
spi_rx_operations_def, rx_update_RX0_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_fetch_data *)
`spi.rx.state = rx_receive_check` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_fetch_data_op_def,
spi_rx_operations_def, rx_receive_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_return *)
`spi.rx.state = rx_receive_check` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_return_op_def,
spi_rx_operations_def, rx_receive_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_check_1 *)
`spi.rx.state = rx_update_RX0` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_check_1_op_def,
spi_rx_operations_def, rx_update_RX0_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_pre_reset *)
`spi.rx.state = rx_update_RX0` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_pre_reset_op_def,
spi_rx_operations_def, rx_update_RX0_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_rx_ready_for_reset *)
`spi.rx.state = rx_receive_check` by METIS_TAC [ref_rel_def, IS_RX_REL_def] >>
rw [spi_abs1_rx_operations_def, spi_abs1_rx_ready_for_reset_op_def,
spi_rx_operations_def, rx_receive_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a lemma: XFER_ENABLE => SPI_ABS1_XFER_ENABLE based on ref_rel *)
val COMB_IMP_ABS1_XFER_ENABLE = store_thm("COMB_IMP_ABS1_XFER_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (XFER_ENABLE spi) ==>
(SPI_ABS1_XFER_ENABLE ds_abs1)``,
rw [XFER_ENABLE_def, SPI_ABS1_XFER_ENABLE_def] >>
`IS_XFER_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
Cases_on `spi.xfer.state` >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_XFER_REL_def] >>
rw [] >>
Cases_on `dr.dr_xfer.state` >>
rw [] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw []);

val ref_rel_spi_xfer_tau = store_thm("ref_rel_spi_xfer_tau",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (XFER_ENABLE spi) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' dr (spi_xfer_operations spi))``,
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
`SPI_ABS1_XFER_ENABLE ds_abs1` by METIS_TAC [COMB_IMP_ABS1_XFER_ENABLE] >>
rw [] >>
FULL_SIMP_TAC std_ss [XFER_ENABLE_def, SPI_ABS1_XFER_ENABLE_def] >|
[(* abs1_xfer_idle *)
`spi.xfer.state = xfer_channel_enabled` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_idle_op_def,
spi_xfer_operations_def, xfer_channel_enabled_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_xfer_trans *)
`spi.xfer.state = xfer_trans_data` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_trans_op_def,
spi_xfer_operations_def, xfer_trans_data_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [] >>
cheat,
(* abs1_xfer_update *)
`spi.xfer.state = xfer_update_RX0` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_update_op_def,
spi_xfer_operations_def, xfer_update_RX0_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_xfer_fetch_data *)
`spi.xfer.state = xfer_check` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_fetch_data_op_def,
spi_xfer_operations_def, xfer_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_xfer_next *)
`spi.xfer.state = xfer_check` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_next_op_def,
spi_xfer_operations_def, xfer_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_xfer_next_write *)
`spi.xfer.state = xfer_check` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_next_write_op_def,
spi_xfer_operations_def, xfer_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [],
(* abs1_xfer_ready_for_reset *)
`spi.xfer.state = xfer_check` by METIS_TAC [ref_rel_def, IS_XFER_REL_def] >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_ready_for_reset_op_def,
spi_xfer_operations_def, xfer_check_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bi-simulation: ds_abs1' exists and holds the ref_rel when spi_tau *)
val abs1_comb_hold_ref_rel_spi_tr = store_thm("abs1_comb_hold_ref_rel_spi_tr",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi tau spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
rw [spi_tr_cases] >>
rw [ref_rel_spi_init_tau, ref_rel_spi_tx_tau, 
ref_rel_spi_rx_tau, ref_rel_spi_xfer_tau]);

val _ = export_theory();
