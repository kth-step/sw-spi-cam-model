open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open driver_stateTheory driver_relationTheory driver_callTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_call_lbl";

(* ref_rel holds for call_init label *)
val abs1_comb_hold_ref_rel_call_init = store_thm("abs1_comb_hold_ref_rel_call_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr call_init dr') /\ (spi.init.state = init_start) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 call_init ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[ (* ds_abs1.ds_abs1_init.state = abs1_init_pre *)
METIS_TAC[ref_rel_def, IS_INIT_REL_def],
(* ref_rel ds_abs1' dr' spi*)
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [IS_INIT_REL_def]]);

(* ref_rel holds for call_tx label *)
val abs1_comb_hold_ref_rel_call_tx = store_thm("abs1_comb_hold_ref_rel_call_tx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_tx buffer) dr') /\ (spi.tx.state = tx_idle) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_def, IS_TX_REL_def],
(* check the ref_rel *)
rw [call_tx_ds_abs1_def, call_tx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw [IS_TX_REL_def]]);

(* ref_rel holds for call_rx label *)
val abs1_comb_hold_ref_rel_call_rx = store_thm("abs1_comb_hold_ref_rel_call_rx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (length: num).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_rx length) dr') /\ (spi.rx.state = rx_idle) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_def, IS_RX_REL_def],
(* check the ref_rel *)
rw [call_rx_ds_abs1_def, call_rx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_XFER_REL_def] >>
rw [IS_RX_REL_def]]);

(* ref_rel holds for call_xfer label *)
val abs1_comb_hold_ref_rel_call_xfer = store_thm("abs1_comb_hold_ref_rel_call_xfer",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_xfer buffer) dr') /\ (spi.xfer.state = xfer_idle) ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_def, IS_XFER_REL_def],
(* check the ref_rel *)
rw [call_xfer_ds_abs1_def, call_xfer_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def] >>
rw [IS_XFER_REL_def]]);


val _ = export_theory();
