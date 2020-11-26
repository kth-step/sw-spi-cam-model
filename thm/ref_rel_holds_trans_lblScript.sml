open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

val _ = new_theory "ref_rel_holds_trans_lbl";

(* a help lemma to determine ds_abs1.ds_abs1_tx.state *)
val ref_rel_spi_tx_trans_done = store_thm("ref_rel_spi_tx_trans_done",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (spi.tx.state = tx_trans_done) ==>
(ABS1_TX_LBL_ENABLE ds_abs1)``,
rw [ABS1_TX_LBL_ENABLE_def] >>
`IS_TX_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def] >>
Cases_on `dr.dr_tx.state` >>
rw [] >|
[`spi.tx.state <> tx_not_ready` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_not_ready` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`spi.tx.state <> tx_idle` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_pre` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`spi.tx.state <> tx_idle` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`spi.tx.state <> tx_conf_ready` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(spi.tx.state <> tx_trans_check) /\ (spi.tx.state <> tx_ready_for_trans)` by rw [] >>
`(ds_abs1.ds_abs1_tx.state <> abs1_tx_ready_for_reset) /\
(ds_abs1.ds_abs1_tx.state <> abs1_tx_reset)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`spi.tx.state <> tx_channel_disabled` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_reset` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw []]);

(* bisimulation: ds_abs1' exists for TX label *)
val abs1_comb_hold_ref_rel_TX = store_thm("abs1_comb_hold_ref_rel_TX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi (TX data) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (TX data) ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
rw [spi_tr_cases] >>
`ABS1_TX_LBL_ENABLE ds_abs1` by METIS_TAC[ref_rel_spi_tx_trans_done] >>
rw [ds_abs1_tr_cases] >|
[(* output data equals *)
rw [tx_trans_done_op_value_def, tx_trans_done_op_def, 
abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def] >>
METIS_TAC[ref_rel_def, ABS1_TX_LBL_ENABLE_def],
(* ref_rel holds *)
FULL_SIMP_TAC std_ss [ABS1_TX_LBL_ENABLE_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_trans_done_op_state_def, tx_trans_done_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for TX label *)
val comb_abs1_hold_ref_rel_TX = store_thm("comb_abs1_hold_ref_rel_TX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ABS1_TX_LBL_ENABLE ds_abs1) ==>
?dr' spi'. (local_tr (dr, spi) (TX (abs1_tx_trans_done_op_value ds_abs1)) (dr', spi')) /\
(ref_rel (abs1_tx_trans_done_op_state ds_abs1) dr' spi')``,
rw [local_tr_cases, spi_tr_cases] >|
[`spi.tx.state = tx_trans_done` by METIS_TAC[ABS1_TX_LBL_ENABLE_def, ref_rel_def, IS_TX_REL_def] >>
rw [abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def,
 tx_trans_done_op_value_def, tx_trans_done_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, ABS1_TX_LBL_ENABLE_def],
METIS_TAC [ABS1_TX_LBL_ENABLE_def, ref_rel_def, IS_TX_REL_def],
`spi.tx.state = tx_trans_done` by METIS_TAC[ABS1_TX_LBL_ENABLE_def, ref_rel_def, IS_TX_REL_def] >>
rw [abs1_tx_trans_done_op_state_def, abs1_tx_trans_done_op_def,
tx_trans_done_op_state_def, tx_trans_done_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, ABS1_TX_LBL_ENABLE_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a subgoal for bisimulation RX label proof *)
val ref_rel_spi_rx_receive_data = store_thm("ref_rel_spi_rx_receive_data",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (spi.rx.state = rx_receive_data) ==>
ABS1_RX_LBL_ENABLE ds_abs1``,
rw [ABS1_RX_LBL_ENABLE_def] >>
`IS_RX_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_RX_REL_def] >>
Cases_on `dr.dr_rx.state` >>
rw [] >|
[`spi.rx.state <> rx_not_ready` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_not_ready` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[],
`spi.rx.state <> rx_idle` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_pre` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[],
`spi.rx.state <> rx_idle` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[],
`(spi.rx.state <> rx_conf_ready) ` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[],
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[],
`spi.rx.state <> rx_channel_disabled` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_reset` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw[]]);


(* bisimulation: ds_abs1' exists for RX label *)
val abs1_comb_hold_ref_rel_RX = store_thm("abs1_comb_hold_ref_rel_RX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi (RX data) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (RX data) ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
rw [spi_tr_cases, ds_abs1_tr_cases] >|
[METIS_TAC [ref_rel_spi_rx_receive_data],
`ABS1_RX_LBL_ENABLE ds_abs1` by METIS_TAC[ref_rel_spi_rx_receive_data] >>
FULL_SIMP_TAC std_ss [ABS1_RX_LBL_ENABLE_def] >>
rw [abs1_rx_receive_data_op_def, rx_receive_data_op_def, abs1_rx_receive_op_def,
abs1_rx_done_op_def, abs1_rx_last_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for RX label *)
val comb_abs1_hold_ref_rel_RX = store_thm("comb_abs1_hold_ref_rel_RX",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option).
(ref_rel ds_abs1 dr spi) /\ (ABS1_RX_LBL_ENABLE ds_abs1) ==>
?dr' spi'. local_tr (dr,spi) (RX data) (dr', spi') /\
(ref_rel (abs1_rx_receive_data_op ds_abs1 data) dr' spi')``,
rw [local_tr_cases, spi_tr_cases] >|
[METIS_TAC [ref_rel_def, IS_RX_REL_def, ABS1_RX_LBL_ENABLE_def],
`spi.rx.state = rx_receive_data` by METIS_TAC[ref_rel_def, IS_RX_REL_def, ABS1_RX_LBL_ENABLE_def] >>
FULL_SIMP_TAC std_ss [ABS1_RX_LBL_ENABLE_def] >>
rw [abs1_rx_receive_data_op_def, abs1_rx_receive_op_def,
abs1_rx_last_op_def, abs1_rx_done_op_def, rx_receive_data_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a subgoal for bisimulation XFER label *)
val ref_rel_spi_xfer_exchange_data = store_thm("ref_rel_spi_xfer_exchange_data",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (spi.xfer.state = xfer_exchange_data) ==>
ds_abs1.ds_abs1_xfer.state = abs1_xfer_exchange``,
rw [] >>
`IS_XFER_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_XFER_REL_def] >>
Cases_on `dr.dr_xfer.state` >>
rw [] >|
[`spi.xfer.state <> xfer_not_ready` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_not_ready` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`spi.xfer.state <> xfer_idle` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_pre` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`spi.xfer.state <> xfer_idle` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`spi.xfer.state <> xfer_conf_ready` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(spi.xfer.state <> xfer_channel_enabled) /\ (spi.xfer.state <> xfer_ready_for_trans) /\
 (spi.xfer.state <> xfer_check)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle) /\ 
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_prepare) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_next)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(spi.xfer.state <> xfer_channel_enabled) /\ (spi.xfer.state <> xfer_ready_for_trans) /\
 (spi.xfer.state <> xfer_check)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle) /\ 
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_prepare) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_next)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(spi.xfer.state <> xfer_ready_for_trans) /\ (spi.xfer.state <> xfer_check)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_trans) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_next_write)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`spi.xfer.state <> xfer_data_ready` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_fetch_data` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(spi.xfer.state <> xfer_ready_for_trans) /\ (spi.xfer.state <> xfer_check)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_fetch_data) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_done)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(spi.xfer.state <> xfer_ready_for_trans) /\ (spi.xfer.state <> xfer_check)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_ready_for_reset) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_reset)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`spi.xfer.state <> xfer_channel_disabled` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_reset` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw []]);


(* bisimulation: ds_abs1' holds for XFER label *)
val abs1_comb_hold_ref_rel_XFER = store_thm("abs1_comb_hold_ref_rel_XFER",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option) (dataOUT:word8 option).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi (XFER dataIN dataOUT) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (XFER dataIN dataOUT) ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
rw [spi_tr_cases] >>
`ds_abs1.ds_abs1_xfer.state = abs1_xfer_exchange` by METIS_TAC[ref_rel_spi_xfer_exchange_data] >>
rw [ds_abs1_tr_cases] >|
[(* output data equals *)
rw [xfer_exchange_data_op_value_def, xfer_exchange_data_op_def,
abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_def] >>
METIS_TAC[ref_rel_def],
(* ref_rel holds *)
rw [xfer_exchange_data_op_state_def, xfer_exchange_data_op_def,
abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for XFER label *)
val comb_abs1_hold_ref_rel_XFER = store_thm("comb_abs1_hold_ref_rel_XFER",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1.ds_abs1_xfer.state = abs1_xfer_exchange) ==>
?dr' spi'. (local_tr (dr, spi) (XFER dataIN (abs1_xfer_exchange_op_value 
ds_abs1 dataIN)) (dr', spi')) /\ 
(ref_rel (abs1_xfer_exchange_op_state ds_abs1 dataIN) dr' spi')``,
rw [local_tr_cases, spi_tr_cases] >|
[`spi.xfer.state = xfer_exchange_data` by METIS_TAC[ref_rel_def, IS_XFER_REL_def] >>
rw [abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_def,
xfer_exchange_data_op_value_def, xfer_exchange_data_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def],
METIS_TAC [ref_rel_def, IS_XFER_REL_def],
`spi.xfer.state = xfer_exchange_data` by METIS_TAC[ref_rel_def, IS_XFER_REL_def] >>
rw [abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def,
xfer_exchange_data_op_state_def, xfer_exchange_data_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

val _ = export_theory();
