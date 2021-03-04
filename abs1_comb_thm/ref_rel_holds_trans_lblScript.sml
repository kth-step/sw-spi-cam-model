open HolKernel bossLib boolLib Parse wordsLib;
open SPI_stateTheory SPI_relationTheory SPI_data_trTheory driver_stateTheory driver_relationTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory;

val _ = new_theory "ref_rel_holds_trans_lbl";

(* If spi.state = tx_trans_done or tx_trans_next, then ds_abs1 is also able to perform TX label transition *)
val spi_tx_trans_done_imply_abs1_tx_enable = store_thm("spi_tx_trans_done_imply_abs1_tx_enable",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ 
(spi.state = tx_trans_done \/ spi.state = tx_trans_next) ==>
(ABS1_TX_LBL_ENABLE ds_abs1)``,
rw [ABS1_TX_LBL_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw []);

(* ds_abs1' exists for TX label *)
val comb_abs1_hold_ref_rel_TX = store_thm("comb_abs1_hold_ref_rel_TX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi_tr spi (TX data) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (TX data) ds_abs1') /\ (ref_rel ds_abs1' (dr, spi'))``,
rw [spi_tr_cases] >>
`ABS1_TX_LBL_ENABLE ds_abs1` by METIS_TAC [spi_tx_trans_done_imply_abs1_tx_enable] >>
rw [ds_abs1_tr_cases] >|
[(* output data equals when spi.state = tx_trans_done *)
rw [tx_TX_op_value_def, tx_TX_op_def, tx_trans_done_op_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
METIS_TAC[ref_rel_def, ABS1_TX_LBL_ENABLE_def],
(* ref_rel holds when spi.state = tx_trans_done *)
fs [ABS1_TX_LBL_ENABLE_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_done_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* output data equals when spi.state = tx_trans_next *)
rw [tx_TX_op_value_def, tx_TX_op_def, tx_trans_next_op_def,
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
METIS_TAC[ref_rel_def, ABS1_TX_LBL_ENABLE_def],
(* ref_rel holds when spi.state = tx_trans_next *)
FULL_SIMP_TAC std_ss [ABS1_TX_LBL_ENABLE_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_next_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);

(* (dr',spi') exists for TX label *)
val abs1_comb_hold_ref_rel_TX = store_thm("abs1_comb_hold_ref_rel_TX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (ABS1_TX_LBL_ENABLE ds_abs1) ==>
?dr' spi'. (local_tr (dr, spi) (TX (abs1_tx_trans_done_op_value ds_abs1)) (dr', spi')) /\
(ref_rel (abs1_tx_trans_done_op_state ds_abs1) (dr', spi'))``,
rw [local_tr_cases, spi_tr_cases] >|
[`spi.state = tx_trans_done \/ spi.state = tx_trans_next` 
by METIS_TAC [ABS1_TX_LBL_ENABLE_def, ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def, 
tx_TX_op_value_def, tx_TX_op_def, tx_trans_done_op_def, tx_trans_next_op_def] >>
fs [ref_rel_def, ABS1_TX_LBL_ENABLE_def],
METIS_TAC [ABS1_TX_LBL_ENABLE_def, ref_rel_def, IS_STATE_REL_def],
fs [ABS1_TX_LBL_ENABLE_def] >|
[(* abs1_tx_done_1 *)
`spi.state = tx_trans_done` by METIS_TAC[ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_done_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_done_2 *)
`spi.state = tx_trans_done` by METIS_TAC[ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_done_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_next *)
`spi.state = tx_trans_next` by METIS_TAC[ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_next_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* abs1_tx_last *)
`spi.state = tx_trans_next` by METIS_TAC[ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_TX_op_state_def, tx_TX_op_def, tx_trans_next_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]]);



(* If spi.state = rx_receive_data, then abs1 is able to process RX label as well. *)
val spi_rx_receive_data_imply_abs1_rx_enable = store_thm("spi_rx_receive_data_imply_abs1_rx_enable",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = rx_receive_data) ==>
ABS1_RX_LBL_ENABLE ds_abs1``,
rw [ABS1_RX_LBL_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw []);

(* ds_abs1' exists for RX label *)
val comb_abs1_hold_ref_rel_RX = store_thm("comb_abs1_hold_ref_rel_RX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi_tr spi (RX data) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (RX data) ds_abs1') /\ 
(ref_rel ds_abs1' (dr, spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases] >-
(METIS_TAC [spi_rx_receive_data_imply_abs1_rx_enable]) >>
`ABS1_RX_LBL_ENABLE ds_abs1` by METIS_TAC [spi_rx_receive_data_imply_abs1_rx_enable] >>
fs [ABS1_RX_LBL_ENABLE_def] >>
rw [abs1_rx_receive_data_op_def, rx_receive_data_op_def, abs1_rx_receive_op_def,
abs1_rx_fetch_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for RX label *)
val abs1_comb_hold_ref_rel_RX = store_thm("abs1_comb_hold_ref_rel_RX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option).
(ref_rel ds_abs1 (dr, spi)) /\ (ABS1_RX_LBL_ENABLE ds_abs1) /\
(data <> NONE) ==>
?dr' spi'. local_tr (dr,spi) (RX data) (dr', spi') /\
(ref_rel (abs1_rx_receive_data_op ds_abs1 data) (dr', spi'))``,
rw [local_tr_cases, spi_tr_cases] >-
(METIS_TAC [ref_rel_def, IS_STATE_REL_def, ABS1_RX_LBL_ENABLE_def]) >>
`spi.state = rx_receive_data` by METIS_TAC[ref_rel_def, IS_STATE_REL_def, ABS1_RX_LBL_ENABLE_def] >>
fs [ABS1_RX_LBL_ENABLE_def] >>
rw [abs1_rx_receive_data_op_def, abs1_rx_receive_op_def,
abs1_rx_fetch_data_op_def, rx_receive_data_op_def] >> 
fs [ref_rel_def, IS_STATE_REL_def]);



(* If spi.state = xfer_exchange_data, then abs1.state = abs1_xfer_exchange_data *)
val spi_xfer_exchange_data_imply_abs1_xfer_enable = store_thm("spi_xfer_exchange_data_imply_abs1_xfer_eanble",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi.state = xfer_exchange_data) ==>
ds_abs1.state = abs1_xfer_exchange``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw []);

(* ds_abs1' holds for XFER label *)
val comb_abs1_hold_ref_rel_XFER = store_thm("comb_abs1_hold_ref_rel_XFER",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option) (dataOUT:word8 option) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (spi_tr spi (XFER dataIN dataOUT) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (XFER dataIN dataOUT) ds_abs1') /\ 
(ref_rel ds_abs1' (dr, spi'))``,
rw [spi_tr_cases] >>
`ds_abs1.state = abs1_xfer_exchange` by METIS_TAC[spi_xfer_exchange_data_imply_abs1_xfer_enable] >>
rw [ds_abs1_tr_cases] >-
((* output data equals *)
rw [xfer_exchange_data_op_value_def, xfer_exchange_data_op_def,
abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_def] >>
METIS_TAC[ref_rel_def]) >>
(* ref_rel holds *)
rw [xfer_exchange_data_op_state_def, xfer_exchange_data_op_def,
abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for XFER label *)
val abs1_comb_hold_ref_rel_XFER = store_thm("abs1_comb_hold_ref_rel_XFER",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option).
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_exchange) /\
(dataIN <> NONE) ==>
?dr' spi'. (local_tr (dr, spi) (XFER dataIN (abs1_xfer_exchange_op_value 
ds_abs1 dataIN)) (dr', spi')) /\ 
(ref_rel (abs1_xfer_exchange_op_state ds_abs1 dataIN) (dr', spi'))``,
rw [local_tr_cases, spi_tr_cases] >|
[`spi.state = xfer_exchange_data` by METIS_TAC[ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_def,
xfer_exchange_data_op_value_def, xfer_exchange_data_op_def] >>
fs [ref_rel_def],
METIS_TAC [ref_rel_def, IS_STATE_REL_def],
`spi.state = xfer_exchange_data` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
rw [abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def,
xfer_exchange_data_op_state_def, xfer_exchange_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]);

val _ = export_theory();
