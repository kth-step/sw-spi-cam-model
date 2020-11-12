open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open driver_stateTheory driver_relationTheory driver_callTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_call_lbl";

(* a lemma for call_init label *)
val ref_rel_dr_init_pre = store_thm("ref_rel_dr_init_pre",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_init.state = dr_init_pre) ==>
ds_abs1.ds_abs1_init.state = abs1_init_pre``,
rw [] >>
`IS_INIT_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def] >|
[Cases_on `spi.init.state` >>
rw [] >|
[`(dr.dr_init.state <> dr_init_read_req) /\ (dr.dr_init.state <> dr_init_check_rep)` by rw [] >>
`ds_abs1.ds_abs1_init.state <> abs1_init_start` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw [],
`(dr.dr_init.state <> dr_init_read_req) /\ 
 (dr.dr_init.state <> dr_init_check_rep) /\
 (dr.dr_init.state <> dr_init_setting)` by rw [] >>
`(ds_abs1.ds_abs1_init.state <> abs1_init_check) /\
 (ds_abs1.ds_abs1_init.state <> abs1_init_done)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw [],
Cases_on `ds_abs1.ds_abs1_init.state` >>
rw []],
FULL_SIMP_TAC std_ss [] >>
rw []]);

(* bisimulation: ds_abs1' exits for call_init label *)
val abs1_comb_hold_ref_rel_call_init = store_thm("abs1_comb_hold_ref_rel_call_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr call_init dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 call_init ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[ (* ds_abs1.ds_abs1_init.state = abs1_init_pre *)
METIS_TAC[ref_rel_dr_init_pre],
(* ref_rel ds_abs1' dr' spi*)
`ds_abs1.ds_abs1_init.state = abs1_init_pre` by METIS_TAC [ref_rel_dr_init_pre] >>
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def, IS_INIT_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for call_init *)
val comb_abs1_hold_ref_rel_call_init = store_thm("comb_abs1_hold_ref_rel_call_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 call_init ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) call_init (dr', spi')) /\
(ref_rel ds_abs1' dr' spi')``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_INIT_REL_def],
rw [call_init_ds_abs1_def, call_init_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [IS_INIT_REL_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a lemma for call_tx label *)
val ref_rel_dr_tx_pre = store_thm("ref_rel_dr_tx_pre",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_tx.state = dr_tx_pre) ==>
ds_abs1.ds_abs1_tx.state = abs1_tx_pre``,
rw [] >>
`IS_TX_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def] >>
Cases_on `spi.tx.state` >>
rw [] >|
[`dr.dr_tx.state <> dr_tx_conf_issued` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(dr.dr_tx.state <> dr_tx_read_txs) /\ (dr.dr_tx.state <> dr_tx_check_txs)` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(dr.dr_tx.state <> dr_tx_read_txs) /\ (dr.dr_tx.state <> dr_tx_check_txs) /\
 (dr.dr_tx.state <> dr_tx_write_data) /\ (dr.dr_tx.state <> dr_tx_read_eot) /\
 (dr.dr_tx.state <> dr_tx_check_eot) /\ (dr.dr_tx.state <> dr_tx_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_tx.state <> abs1_tx_prepare) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_trans) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_check_2) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_reset)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(dr.dr_tx.state <> dr_tx_read_txs) /\ (dr.dr_tx.state <> dr_tx_check_txs) /\
 (dr.dr_tx.state <> dr_tx_read_eot) /\ (dr.dr_tx.state <> dr_tx_check_eot)` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_trans` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(dr.dr_tx.state <> dr_tx_read_txs) /\ (dr.dr_tx.state <> dr_tx_check_txs) /\
 (dr.dr_tx.state <> dr_tx_write_data) /\ (dr.dr_tx.state <> dr_tx_read_eot) /\
 (dr.dr_tx.state <> dr_tx_check_eot)` by rw [] >>
`(ds_abs1.ds_abs1_tx.state <> abs1_tx_done_1) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_done_2) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_done_3)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`(dr.dr_tx.state <> dr_tx_read_txs) /\ (dr.dr_tx.state <> dr_tx_check_txs) /\
 (dr.dr_tx.state <> dr_tx_write_data) /\ (dr.dr_tx.state <> dr_tx_read_eot) /\
 (dr.dr_tx.state <> dr_tx_check_eot) /\ (dr.dr_tx.state <> dr_tx_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_tx.state <> abs1_tx_check_1) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_check_3) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_next) /\
 (ds_abs1.ds_abs1_tx.state <> abs1_tx_ready_for_reset)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw [],
`dr.dr_tx.state <> dr_tx_reset_conf` by rw [] >>
`ds_abs1.ds_abs1_tx.state <> abs1_tx_reset` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_tx.state` >>
rw []]);

(* bisimulation: ds_abs1' exists for call_tx label *)
val abs1_comb_hold_ref_rel_call_tx = store_thm("abs1_comb_hold_ref_rel_call_tx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_tx buffer) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_dr_tx_pre],
(* check the ref_rel *)
`ds_abs1.ds_abs1_tx.state = abs1_tx_pre` by METIS_TAC[ref_rel_dr_tx_pre] >>
rw [call_tx_ds_abs1_def, call_tx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for call_tx label *)
val comb_abs1_hold_ref_rel_call_tx = store_thm("comb_abs1_hold_ref_rel_call_tx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1') /\
(buffer <> []) ==>
?dr' spi'. (local_tr (dr, spi) (call_tx buffer) (dr', spi')) /\
(ref_rel ds_abs1' dr' spi')``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_TX_REL_def],
rw [call_tx_ds_abs1_def, call_tx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [IS_TX_REL_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a lemma for call_rx label *)
val ref_rel_dr_rx_pre = store_thm("ref_rel_dr_rx_pre",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_rx.state = dr_rx_pre) ==>
ds_abs1.ds_abs1_rx.state = abs1_rx_pre``,
rw [] >>
`IS_RX_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_RX_REL_def] >>
Cases_on `spi.rx.state` >>
rw [] >|
[`dr.dr_rx.state <> dr_rx_conf_issued` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`(dr.dr_rx.state <> dr_rx_read_rxs) /\ (dr.dr_rx.state <> dr_rx_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_idle` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`(dr.dr_rx.state <> dr_rx_read_rxs) /\ (dr.dr_rx.state <> dr_rx_check_rxs) /\
 (dr.dr_rx.state <> dr_rx_fetch_data) /\ (dr.dr_rx.state <> dr_rx_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_rx.state <> abs1_rx_receive) /\
 (ds_abs1.ds_abs1_rx.state <> abs1_rx_done) /\
 (ds_abs1.ds_abs1_rx.state <> abs1_rx_reset)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`(dr.dr_rx.state <> dr_rx_read_rxs) /\ (dr.dr_rx.state <> dr_rx_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_update` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`(dr.dr_rx.state <> dr_rx_read_rxs) /\ (dr.dr_rx.state <> dr_rx_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_ready` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`(dr.dr_rx.state <> dr_rx_read_rxs) /\ (dr.dr_rx.state <> dr_rx_check_rxs) /\
 (dr.dr_rx.state <> dr_rx_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_rx.state <> abs1_rx_return) /\
 (ds_abs1.ds_abs1_rx.state <> abs1_rx_ready_for_reset)` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw [],
`dr.dr_rx.state <> dr_rx_reset_conf` by rw [] >>
`ds_abs1.ds_abs1_rx.state <> abs1_rx_reset` by METIS_TAC [] >>
Cases_on `ds_abs1.ds_abs1_rx.state` >>
rw []]);


(* bisimulation: ds_abs1' exists for call_rx label *)
val abs1_comb_hold_ref_rel_call_rx = store_thm("abs1_comb_hold_ref_rel_call_rx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (length: num).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_rx length) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_dr_rx_pre],
(* check the ref_rel *)
`ds_abs1.ds_abs1_rx.state = abs1_rx_pre` by METIS_TAC[ref_rel_dr_rx_pre] >>
rw [call_rx_ds_abs1_def, call_rx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (ds',spi') exists for call_rx label *)
val comb_abs1_hold_ref_rel_call_rx = store_thm("comb_abs1_hold_ref_rel_call_rx",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (length: num).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1.ds_abs1_rx.state = abs1_rx_pre) /\
(length > 0) ==>
?dr' spi'. (local_tr (dr, spi) (call_rx length) (dr', spi')) /\ 
(ref_rel (call_rx_ds_abs1 ds_abs1 length) dr' spi')``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_RX_REL_def],
rw [call_rx_ds_abs1_def, call_rx_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [IS_RX_REL_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* a help lemmas for call_xfer label *)
val ref_rel_dr_xfer_pre = store_thm("ref_rel_dr_xfer_pre",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (dr.dr_xfer.state = dr_xfer_pre) ==>
ds_abs1.ds_abs1_xfer.state = abs1_xfer_pre``,
rw [] >>
`IS_XFER_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_XFER_REL_def] >>
Cases_on `spi.xfer.state` >>
rw [] >|
[`dr.dr_xfer.state <> dr_xfer_conf_issued` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_txs) /\ (dr.dr_xfer.state <> dr_xfer_check_txs)` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_idle` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_txs) /\ (dr.dr_xfer.state <> dr_xfer_check_txs) /\
 (dr.dr_xfer.state <> dr_xfer_write_dataO) /\ (dr.dr_xfer.state <> dr_xfer_fetch_dataI) /\
 (dr.dr_xfer.state <> dr_xfer_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_prepare) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_trans) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_done) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_reset)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_rxs) /\ (dr.dr_xfer.state <> dr_xfer_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_trans` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_rxs) /\ (dr.dr_xfer.state <> dr_xfer_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_exchange` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_rxs) /\ (dr.dr_xfer.state <> dr_xfer_check_rxs)` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_update` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_rxs) /\ (dr.dr_xfer.state <> dr_xfer_check_rxs) /\
 (dr.dr_xfer.state <> dr_xfer_read_rx0)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_ready) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_fetch_data)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`(dr.dr_xfer.state <> dr_xfer_read_txs) /\ (dr.dr_xfer.state <> dr_xfer_check_txs) /\
 (dr.dr_xfer.state <> dr_xfer_fetch_dataI) /\ (dr.dr_xfer.state <> dr_xfer_write_dataO) /\
 (dr.dr_xfer.state <> dr_xfer_issue_disable)` by rw [] >>
`(ds_abs1.ds_abs1_xfer.state <> abs1_xfer_fetch_data) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_next) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_next_write) /\
 (ds_abs1.ds_abs1_xfer.state <> abs1_xfer_ready_for_reset)` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw [],
`dr.dr_xfer.state <> dr_xfer_reset_conf` by rw [] >>
`ds_abs1.ds_abs1_xfer.state <> abs1_xfer_reset` by METIS_TAC[] >>
Cases_on `ds_abs1.ds_abs1_xfer.state` >>
rw []]);

(* bisimulation: ds_abs1' exists for call_xfer label *)
val abs1_comb_hold_ref_rel_call_xfer = store_thm("abs1_comb_hold_ref_rel_call_xfer",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (driver_tr dr (call_xfer buffer) dr') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') /\ (ref_rel ds_abs1' dr' spi)``,
rw [driver_tr_cases, ds_abs1_tr_cases] >|
[(* check the state *)
METIS_TAC[ref_rel_dr_xfer_pre],
(* check the ref_rel *)
`ds_abs1.ds_abs1_xfer.state = abs1_xfer_pre` by METIS_TAC[ref_rel_dr_xfer_pre] >>
rw [call_xfer_ds_abs1_def, call_xfer_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

(* bisimulation: (dr',spi') exists for call_xfer label *)
val comb_abs1_hold_ref_rel_call_xfer = store_thm("comb_abs1_hold_ref_rel_call_xfer",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (buffer:word8 list).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1') /\
(buffer <> []) ==>
?dr' spi'. (local_tr (dr, spi) (call_xfer buffer) (dr', spi')) /\
(ref_rel ds_abs1' dr' spi')``,
rw [ds_abs1_tr_cases, local_tr_cases, driver_tr_cases] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_XFER_REL_def],
rw [call_xfer_ds_abs1_def, call_xfer_dr_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [IS_XFER_REL_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []]);

val _ = export_theory();
