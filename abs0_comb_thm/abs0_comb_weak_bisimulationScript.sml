open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory abs_relTheory driver_stateTheory SPI_stateTheory ds_abs1_stateTheory ds_abs1_relTheory ref_relTheory driver_relationTheory ds_abs0_relTheory weak_bisimulationTheory abs1_comb_weak_bisimulationTheory abs_weak_bisimulationTheory;

val _ = new_theory "abs0_comb_weak_bisimulation";

(* some lemmas about n_tau_tr *)
val n_tau_tr_last = store_thm ("n_tau_tr_last",
``!tr s s' s'' lbl n.
n_tau_tr n tr s tau s'' /\ tr s'' lbl s' ==>
?s'''. tr s tau s''' /\ n_tau_tr n tr s''' lbl s'``, 
Induct_on `n` >>
rw [n_tau_tr_def] >-
(Q.EXISTS_TAC `s''` >> rw []) >>
Q.EXISTS_TAC `s'''` >> rw [] >>
METIS_TAC []);

val n_tau_tr_plus = store_thm ("n_tau_tr_plus",
``!tr s s' s'' n1 n2 lbl.
n_tau_tr n2 tr s tau s'' /\ n_tau_tr n1 tr s'' lbl s' ==>
n_tau_tr (SUC (n1 + n2)) tr s lbl s'``,
Induct_on `n1` >>
Induct_on `n2` >>
rw [n_tau_tr_def] >|[
Q.EXISTS_TAC `s''` >> rw [],
Q.EXISTS_TAC `s'''` >> rw [] >> METIS_TAC [n_tau_tr_last],
Q.EXISTS_TAC `s''` >> rw [] >> METIS_TAC [n_tau_tr_last],
Q.EXISTS_TAC `s'''` >> rw [] >> 
`n_tau_tr (SUC n1) tr s'' lbl s' = ?s. tr s'' tau s /\ n_tau_tr n1 tr s lbl s'` by rw [n_tau_tr_def] >>
`n_tau_tr (SUC n1) tr s'' lbl s'` by METIS_TAC [] >> 
`SUC n1 + SUC n2 = SUC (SUC n1 + n2)` by rw [] >>
METIS_TAC []]);

val n_tau_tr_exsists = store_thm ("n_tau_tr_exsists",
``!dr spi n ds_abs1' lbl ds_abs1.
n_tau_tr n ds_abs1_tr ds_abs1 lbl ds_abs1' /\ ref_rel ds_abs1 (dr,spi) ==>
?n1 dr' spi'. n_tau_tr n1 local_tr (dr,spi) lbl (dr',spi') /\ ref_rel ds_abs1' (dr',spi')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(`(?dr' spi'. (local_tr (dr, spi) lbl (dr', spi')) /\ (ref_rel ds_abs1' (dr',spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) lbl (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))` by METIS_TAC [abs1_comb_weak_simulation] >-
(Q.EXISTS_TAC `0` >>
Q.EXISTS_TAC `dr'` >>
Q.EXISTS_TAC `spi'` >>
rw [n_tau_tr_def]) >>
METIS_TAC []) >>
`(?dr'' spi''. (local_tr (dr,spi) tau (dr'', spi'')) /\ (ref_rel s'' (dr'', spi''))) \/
(?n2 dr'' spi''. (n_tau_tr n2 local_tr (dr, spi) tau (dr'', spi'')) /\
(ref_rel s'' (dr'', spi'')))` by METIS_TAC [abs1_comb_weak_simulation_tau] >>
`?n1 dr' spi'.n_tau_tr n1 local_tr (dr'',spi'') lbl (dr',spi') /\
ref_rel ds_abs1' (dr',spi')` by METIS_TAC [] >-
(Q.EXISTS_TAC `SUC n1` >>
Q.EXISTS_TAC `dr'` >>
Q.EXISTS_TAC `spi'` >>
rw [n_tau_tr_def] >>
Q.EXISTS_TAC `(dr'',spi'')` >>
rw []) >>
Q.EXISTS_TAC `SUC (n1 + n2)` >>
Q.EXISTS_TAC `dr'` >>
Q.EXISTS_TAC `spi'` >>
rw [] >>
METIS_TAC [n_tau_tr_plus]);

val n_tau_tr_local_global_tr_first = store_thm("n_tau_tr_local_global_tr_first",
``!n dr0 spi0 dr1 spi1 dr0' spi0' lbl.
n_tau_tr n local_tr (dr0,spi0) lbl (dr0',spi0') /\
(!d. lbl <> TX d) /\ (!d. lbl <> RX d) /\ (!d0 d1. lbl <> XFER d0 d1) ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1,spi1)``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
fs [local_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val n_tau_tr_local_global_tr_second = store_thm("n_tau_tr_local_global_tr_second",
``!n dr0 spi0 dr1 spi1 dr1' spi1' lbl.
n_tau_tr n local_tr (dr1,spi1) lbl (dr1',spi1') /\
(!d. lbl <> TX d) /\ (!d. lbl <> RX d) /\ (!d0 d1. lbl <> XFER d0 d1) ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0,spi0,dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
fs [local_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val d0_TX_d1_RX_n_tau_tr = store_thm("d0_TX_d1_RX_n_tau_tr",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (RX data) (dr1',spi1') /\
local_tr (dr0,spi0) (TX data) (dr0',spi0') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val d1_TX_d0_RX_n_tau_tr = store_thm("d1_TX_d0_RX_n_tau_tr",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr0,spi0) (RX data) (dr0',spi0') /\
local_tr (dr1,spi1) (TX data) (dr1',spi1') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val d0_TX_n_tau_tr_d1_RX = store_thm("d0_TX_n_tau_tr_d1_RX",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
local_tr (dr1,spi1) (RX data) (dr1',spi1') /\
n_tau_tr n local_tr (dr0,spi0) (TX data) (dr0',spi0') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val d1_TX_n_tau_tr_d0_RX = store_thm("d1_TX_n_tau_tr_d0_RX",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (TX data) (dr1',spi1') /\
local_tr (dr0,spi0) (RX data) (dr0',spi0') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val d0_TX_d1_RX_n_plus_n' = store_thm("d0_TX_d1_RX_n_plus_n'",
``!n n' dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (RX data) (dr1',spi1') /\
n_tau_tr n' local_tr (dr0,spi0) (TX data) (dr0',spi0') ==>
n_tau_tr (n + n') global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
Induct_on `n'` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
`!dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (RX data) (dr1',spi1') /\
n_tau_tr 0 local_tr (dr0,spi0) (TX data) (dr0',spi0') ==>
n_tau_tr (n + 0) global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')` by METIS_TAC [] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >>
`SUC n + SUC n' = SUC (SUC (n + n'))` by rw [] >>
rw [n_tau_tr_def] >>
Cases_on `s''` >>
Cases_on `s'''` >>
Q.EXISTS_TAC `(q',r',dr1,spi1)` >>
rw [global_tr_cases] >>
Q.EXISTS_TAC `(q',r',q,r)` >> 
fs [] >>
METIS_TAC []);

val d1_TX_d0_RX_n_plus_n' = store_thm("d0_TX_d1_RX_n_plus_n'",
``!n n' dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (TX data) (dr1',spi1') /\
n_tau_tr n' local_tr (dr0,spi0) (RX data) (dr0',spi0') ==>
n_tau_tr (n + n') global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
Induct_on `n'` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
`!dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' data.
n_tau_tr n local_tr (dr1,spi1) (TX data) (dr1',spi1') /\
n_tau_tr 0 local_tr (dr0,spi0) (RX data) (dr0',spi0') ==>
n_tau_tr (n + 0) global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')` by METIS_TAC [] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >>
`SUC n + SUC n' = SUC (SUC (n + n'))` by rw [] >>
rw [n_tau_tr_def] >>
Cases_on `s''` >>
Cases_on `s'''` >>
Q.EXISTS_TAC `(q',r',dr1,spi1)` >>
rw [global_tr_cases] >>
Q.EXISTS_TAC `(q',r',q,r)` >> 
fs [] >>
METIS_TAC []);

val XFER_d0_d1_n_tau_tr = store_thm("XFER_d0_d1_n_tau_tr",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' dataI dataO.
n_tau_tr n local_tr (dr1,spi1) (XFER dataO dataI) (dr1',spi1') /\
local_tr (dr0,spi0) (XFER dataI dataO) (dr0',spi0') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val XFER_d0_n_tau_tr_d1 = store_thm("XFER_d0_n_tau_tr_d1",
``!n dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' dataI dataO.
local_tr (dr1,spi1) (XFER dataO dataI) (dr1',spi1') /\
n_tau_tr n local_tr (dr0,spi0) (XFER dataI dataO) (dr0',spi0') ==>
n_tau_tr n global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >>
Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
METIS_TAC []);

val XFER_d0_d1_n_plus_n' = store_thm("XFER_d0_d1_n_plus_n'",
``!n n' dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' dataI dataO.
n_tau_tr n local_tr (dr1,spi1) (XFER dataO dataI) (dr1',spi1') /\
n_tau_tr n' local_tr (dr0,spi0) (XFER dataI dataO) (dr0',spi0') ==>
n_tau_tr (n + n') global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')``,
Induct_on `n` >>
Induct_on `n'` >>
rw [n_tau_tr_def] >-
(rw [global_tr_cases] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(q,r,dr1,spi1)` >>
rw [global_tr_cases] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >-
(Cases_on `s''` >>
Q.EXISTS_TAC `(dr0,spi0,q,r)` >>
rw [global_tr_cases] >>
`!dr0 spi0 dr0' spi0' dr1 spi1 dr1' spi1' dataI dataO.
n_tau_tr n local_tr (dr1,spi1) (XFER dataO dataI) (dr1',spi1') /\
n_tau_tr 0 local_tr (dr0,spi0) (XFER dataI dataO) (dr0',spi0') ==>
n_tau_tr (n + 0) global_tr (dr0,spi0,dr1,spi1) tau (dr0',spi0',dr1',spi1')` by METIS_TAC [] >>
fs [n_tau_tr_def] >>
METIS_TAC []) >>
`SUC n + SUC n' = SUC (SUC (n + n'))` by rw [] >>
rw [n_tau_tr_def] >>
Cases_on `s''` >>
Cases_on `s'''` >>
Q.EXISTS_TAC `(q',r',dr1,spi1)` >>
rw [global_tr_cases] >>
Q.EXISTS_TAC `(q',r',q,r)` >> 
fs [] >>
METIS_TAC []);

(* weak bisimulation of the abs0 and concrete models *)
val weak_bisimulation_abs0_comb = store_thm("weak_bisimulation_abs0_comb",
``weak_bisim abs0_comb_rel ds_abs0_tr local_tr``,
`weak_bisim abs_rel ds_abs0_tr ds_abs1_tr` by rw [weak_bisimulation_abs0_abs1] >>
`weak_bisim ref_rel ds_abs1_tr local_tr` by rw [weak_bisimulation_abs1_comb] >>
fs [weak_bisim_def] >> rw [] >>
Cases_on `s2` >>
fs [abs0_comb_rel_def] >-
((* (dr',spi') exists *)
`(?ds_abs1'.(ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (abs_rel s1' ds_abs1')) \/
(?n ds_abs1'. (n_tau_tr n ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (abs_rel s1' ds_abs1'))` 
by METIS_TAC [abs0_abs1_weak_simulation] >-
(`?s2'. weak_tr local_tr (q,r) lbl s2' /\ ref_rel ds_abs1' s2' ` by METIS_TAC [] >>
Q.EXISTS_TAC `s2'` >>
Cases_on `s2'` >>
rw [abs0_comb_rel_def] >>
Q.EXISTS_TAC `ds_abs1'` >> rw []) >>
`?n1 dr' spi'. n_tau_tr n1 local_tr (q,r) lbl (dr',spi') /\ ref_rel ds_abs1' (dr',spi')` by METIS_TAC [n_tau_tr_exsists] >>
Q.EXISTS_TAC `(dr',spi')` >>
rw [abs0_comb_rel_def, weak_tr_def] >-
(REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n1` >> rw []) >>
Q.EXISTS_TAC `ds_abs1'` >> rw []) >>
(* ds_abs0' exists *)
Cases_on `lbl <> tau` >> 
Cases_on `s2'` >-
(`?ds_abs1'. (ds_abs1_tr ds_abs1 lbl ds_abs1') /\ (ref_rel ds_abs1' (q', r'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?s1'. weak_tr ds_abs0_tr s1 lbl s1' /\ abs_rel s1' ds_abs1'` by METIS_TAC [] >>
Q.EXISTS_TAC `s1'` >>
rw [abs0_comb_rel_def] >>
Q.EXISTS_TAC `ds_abs1'` >> rw []) >>
rw [] >>
`(ref_rel ds_abs1 (q', r')) \/ 
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' (q', r')))` by METIS_TAC [comb_abs1_weak_simulation_tau] >- 
(Q.EXISTS_TAC `s1` >>
rw [abs0_comb_rel_def, weak_tr_def] >>
Q.EXISTS_TAC `ds_abs1` >> rw []) >>
`?s1'. weak_tr ds_abs0_tr s1 tau s1' /\ abs_rel s1' ds_abs1'` by METIS_TAC [] >>
Q.EXISTS_TAC `s1'` >>
rw [abs0_comb_rel_def] >>
Q.EXISTS_TAC `ds_abs1'` >> rw []);

(* global relation shows how 2 spi devices work together.
   weak bisimulation for the global relation of abs0 and concrete models *)
val weak_bisimulation_global_abs0_comb = store_thm("weak_bisimulation_global_abs0_comb",
``weak_bisim global_abs0_comb_rel abs0_global_tr global_tr``,
`weak_bisim abs0_comb_rel ds_abs0_tr local_tr` by rw [weak_bisimulation_abs0_comb] >>
fs [weak_bisim_def] >> rw [] >>
Cases_on `s1` >>
Cases_on `s2` >>
Cases_on `r'` >>
Cases_on `r''` >- 
((* (dr0',spi0',dr1',spi1') exists *)
fs [global_abs0_comb_rel_def, abs0_global_tr_cases] >|
[`?s2'. weak_tr local_tr (q',q'') call_init s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases]) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_init <> TX d) /\
(!d. call_init <> RX d) /\
(!d0 d1. call_init <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') call_init s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases]) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_init <> TX d) /\
(!d. call_init <> RX d) /\
(!d0 d1. call_init <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],
`?s2'. weak_tr local_tr (q',q'') (call_tx buffer) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_tx buffer <> TX d) /\
(!d. call_tx buffer <> RX d) /\
(!d0 d1. call_tx buffer <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') (call_tx buffer) s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_tx buffer <> TX d) /\
(!d. call_tx buffer <> RX d) /\
(!d0 d1. call_tx buffer <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],
`?s2'. weak_tr local_tr (q',q'') (call_rx l) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_rx l <> TX d) /\
(!d. call_rx l <> RX d) /\
(!d0 d1. call_rx l <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') (call_rx l) s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_rx l <> TX d) /\
(!d. call_rx l <> RX d) /\
(!d0 d1. call_rx l <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],
`?s2'. weak_tr local_tr (q',q'') (call_xfer buffer0) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_xfer buffer0 <> TX d) /\
(!d. call_xfer buffer0 <> RX d) /\
(!d0 d1. call_xfer buffer0 <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') (call_xfer buffer1) s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_xfer buffer1 <> TX d) /\
(!d. call_xfer buffer1 <> RX d) /\
(!d0 d1. call_xfer buffer1 <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],
`?s2'. weak_tr local_tr (q',q'') (call_back buffer0) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_back buffer0 <> TX d) /\
(!d. call_back buffer0 <> RX d) /\
(!d0 d1. call_back buffer0 <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') (call_back buffer1) s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. call_back buffer1 <> TX d) /\
(!d. call_back buffer1 <> RX d) /\
(!d0 d1. call_back buffer1 <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],       
`?s2'. weak_tr local_tr (q',q'') tau s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q'''',r'',q''',r')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. tau <> TX d) /\
(!d. tau <> RX d) /\
(!d0 d1. tau <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_first],
`?s2'. weak_tr local_tr (q''',r') tau s2' /\ abs0_comb_rel d1' s2'` by METIS_TAC [] >>
Cases_on `s2'` >>
Q.EXISTS_TAC `(q',q'',q'''',r'')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >>
Q.EXISTS_TAC `n` >>
`(!d. tau <> TX d) /\
(!d. tau <> RX d) /\
(!d0 d1. tau <> XFER d0 d1)` by rw [] >>
METIS_TAC [n_tau_tr_local_global_tr_second],
`?s2'. weak_tr local_tr (q',q'') (TX data) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
`?s2''. weak_tr local_tr (q''',r') (RX data) s2'' /\ abs0_comb_rel d1' s2''` by METIS_TAC [] >>
Cases_on `s2'` >> Cases_on `s2''` >>
Q.EXISTS_TAC `(q'''',r'',q''''',r''')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >|
[Q.EXISTS_TAC `n` >> METIS_TAC [d0_TX_d1_RX_n_tau_tr],
 Q.EXISTS_TAC `n` >> METIS_TAC [d0_TX_n_tau_tr_d1_RX],
 Q.EXISTS_TAC `n' + n` >> METIS_TAC [d0_TX_d1_RX_n_plus_n']],
`?s2'. weak_tr local_tr (q',q'') (RX data) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
`?s2''. weak_tr local_tr (q''',r') (TX data) s2'' /\ abs0_comb_rel d1' s2''` by METIS_TAC [] >>
Cases_on `s2'` >> Cases_on `s2''` >>
Q.EXISTS_TAC `(q'''',r'',q''''',r''')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >|
[Q.EXISTS_TAC `n` >> METIS_TAC [d1_TX_n_tau_tr_d0_RX],
 Q.EXISTS_TAC `n` >> METIS_TAC [d1_TX_d0_RX_n_tau_tr],
 Q.EXISTS_TAC `n' + n` >> METIS_TAC [d1_TX_d0_RX_n_plus_n']],
`?s2'. weak_tr local_tr (q',q'') (XFER dataI dataO) s2' /\ abs0_comb_rel d0' s2'` by METIS_TAC [] >>
`?s2''. weak_tr local_tr (q''',r') (XFER dataO dataI) s2'' /\ abs0_comb_rel d1' s2''` by METIS_TAC [] >>
Cases_on `s2'` >> Cases_on `s2''` >>
Q.EXISTS_TAC `(q'''',r'',q''''',r''')` >>
fs [global_abs0_comb_rel_def, weak_tr_def] >-
(DISJ1_TAC >>
rw [global_tr_cases] >>
METIS_TAC []) >>
REPEAT DISJ2_TAC >|
[Q.EXISTS_TAC `n` >> METIS_TAC [XFER_d0_d1_n_tau_tr],
 Q.EXISTS_TAC `n` >> METIS_TAC [XFER_d0_n_tau_tr_d1],
 Q.EXISTS_TAC `n' + n` >> METIS_TAC [XFER_d0_d1_n_plus_n']]]) >>
(* (d0',d1') exists *)
fs [global_abs0_comb_rel_def, abs0_comb_rel_def, global_tr_cases] >|
[`call_init <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 call_init ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q call_init ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`call_init <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1' call_init ds_abs1'') /\ (ref_rel ds_abs1'' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr r call_init ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(q,ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],
`call_tx buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (call_tx buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (call_tx buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`call_tx buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1' (call_tx buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr r (call_tx buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(q,ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],
`call_rx length <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (call_rx length) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (call_rx length) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`call_rx length <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1' (call_rx length) ds_abs1'') /\ (ref_rel ds_abs1'' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr r (call_rx length) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(q,ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],
`call_xfer buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (call_xfer buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (call_xfer buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`call_xfer buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1' (call_xfer buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr r (call_xfer buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(q,ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],
`call_back buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (call_back buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (call_back buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`call_back buffer <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1' (call_back buffer) ds_abs1'') /\ (ref_rel ds_abs1'' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr r (call_back buffer) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(q,ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],        
`ref_rel ds_abs1 (dr1',spi1') \/
?ds_abs1''. ds_abs1_tr ds_abs1 tau ds_abs1'' /\ ref_rel ds_abs1'' (dr1',spi1')` by METIS_TAC [comb_abs1_weak_simulation_tau] >-
(Q.EXISTS_TAC `(q,r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >>
METIS_TAC []) >>
`abs_rel q ds_abs1'' \/
?ds_abs0'. ds_abs0_tr q tau ds_abs0' /\ abs_rel ds_abs0' ds_abs1''` by METIS_TAC [abs1_abs0_weak_simulation] >-
(Q.EXISTS_TAC `(q,r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >>
METIS_TAC []) >>
Q.EXISTS_TAC `(ds_abs0',r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'` >> rw []],
`ref_rel ds_abs1' (dr2',spi2') \/
?ds_abs1''. ds_abs1_tr ds_abs1' tau ds_abs1'' /\ ref_rel ds_abs1'' (dr2',spi2')` by METIS_TAC [comb_abs1_weak_simulation_tau] >-
(Q.EXISTS_TAC `(q,r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >>
METIS_TAC []) >>
`abs_rel r ds_abs1'' \/
?ds_abs0'. ds_abs0_tr r tau ds_abs0' /\ abs_rel ds_abs0' ds_abs1''` by METIS_TAC [abs1_abs0_weak_simulation] >-
(Q.EXISTS_TAC `(q,r)` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >>
METIS_TAC []) >>
Q.EXISTS_TAC `(q, ds_abs0')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1` >> rw [],
Q.EXISTS_TAC `ds_abs1''` >> rw []],
`TX data <> tau /\ RX data <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (TX data) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs1'''. (ds_abs1_tr ds_abs1' (RX data) ds_abs1''') /\ (ref_rel ds_abs1''' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (TX data) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
`?ds_abs0''. (ds_abs0_tr r (RX data) ds_abs0'') /\ (abs_rel ds_abs0'' ds_abs1''')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',ds_abs0'')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'''` >> rw []],
`TX data <> tau /\ RX data <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (RX data) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs1'''. (ds_abs1_tr ds_abs1' (TX data) ds_abs1''') /\ (ref_rel ds_abs1''' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (RX data) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
`?ds_abs0''. (ds_abs0_tr r (TX data) ds_abs0'') /\ (abs_rel ds_abs0'' ds_abs1''')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',ds_abs0'')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'''` >> rw []],
`XFER dataI dataO <> tau /\ XFER dataO dataI <> tau` by rw [] >>
`?ds_abs1''. (ds_abs1_tr ds_abs1 (XFER dataI dataO) ds_abs1'') /\ (ref_rel ds_abs1'' (dr1', spi1'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs1'''. (ds_abs1_tr ds_abs1' (XFER dataO dataI) ds_abs1''') /\ (ref_rel ds_abs1''' (dr2', spi2'))` by METIS_TAC [comb_abs1_weak_simulation_lbl_not_tau] >>
`?ds_abs0'. (ds_abs0_tr q (XFER dataI dataO) ds_abs0') /\ (abs_rel ds_abs0' ds_abs1'')` by METIS_TAC [abs1_abs0_weak_simulation] >>
`?ds_abs0''. (ds_abs0_tr r (XFER dataO dataI) ds_abs0'') /\ (abs_rel ds_abs0'' ds_abs1''')` by METIS_TAC [abs1_abs0_weak_simulation] >>
Q.EXISTS_TAC `(ds_abs0',ds_abs0'')` >>
rw [global_abs0_comb_rel_def, abs0_comb_rel_def, weak_tr_def] >|
[DISJ1_TAC >>
rw [abs0_global_tr_cases] >>
METIS_TAC [],
Q.EXISTS_TAC `ds_abs1''` >> rw [],
Q.EXISTS_TAC `ds_abs1'''` >> rw []]]);

val _ = export_theory();
