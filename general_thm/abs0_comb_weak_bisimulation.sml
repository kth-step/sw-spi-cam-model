open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory abs_relTheory driver_stateTheory SPI_stateTheory ds_abs1_stateTheory ds_abs1_relTheory ref_relTheory driver_relationTheory ds_abs0_relTheory weak_bisimulationTheory abs1_comb_weak_bisimulationTheory abs_weak_bisimulationTheory;

val _ = new_theory "abs0_comb_weak_bisimulation";

val abs0_comb_rel_def = Define `
abs0_comb_rel (ds_abs0:ds_abs0_state) (dr:driver_state, spi:spi_state) = 
(?ds_abs1:ds_abs1_state. abs_rel ds_abs0 ds_abs1 /\ ref_rel ds_abs1 (dr,spi))`

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

val weak_bisimulation_abs0_comb = store_thm("weak_bisimulation_abs0_comb",
``weak_bisim abs0_comb_rel ds_abs0_tr local_tr``,
`weak_bisim abs_rel ds_abs0_tr ds_abs1_tr` by rw [weak_bisimulation_abs0_abs1] >>
`weak_bisim ref_rel ds_abs1_tr local_tr` by rw [weak_bisimulation_abs1_comb] >>
fs [weak_bisim_def] >>
rw [] >>
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

val _ = export_theory();
