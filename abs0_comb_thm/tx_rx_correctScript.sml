open HolKernel bossLib boolLib Parse listTheory;
open ds_abs0_stateTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_tauTheory ds_abs0_relTheory ds_abs0_initTheory weak_bisimulationTheory abs0_comb_weak_bisimulationTheory;

val _ = new_theory "tx_rx_correct";

(* abs0 tx and rx modes correct, theorem 1: from ready state, two devices can apply tx and rx mode respectively *)
val abs0_tx_rx_calls_correct = store_thm("abs0_tx_rx_calls_correct",
``!d0 d1 l n d0' d1'.
d0.state = abs0_ready /\ d1.state = abs0_ready /\ l <> [] /\ n > 0 ==>
ds_abs0_tr d0 (call_tx l) d0' /\ ds_abs0_tr d1 (call_rx n) d1' ==>
d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = l /\
d0'.ds_abs0_tx.tx_cur_length = 0 /\
d1'.state = abs0_rx_idle /\ d1'.ds_abs0_rx.rx_left_length = n /\
d1'.ds_abs0_rx.rx_data_buffer = []``,
rw [ds_abs0_tr_cases, call_rx_ds_abs0_def, call_tx_ds_abs0_def]);


(* some lemmas for theorem 2 *)
val abs0_tx_rx_first_one_byte = store_thm("abs0_tx_rx_first_one_byte",
``!d0 d1 x l1' n.
d0.state = abs0_tx /\ d0.ds_abs0_tx.tx_data_buffer = x::l1' /\
d0.ds_abs0_tx.tx_cur_length = 0 /\
d1.state = abs0_rx_idle /\ d1.ds_abs0_rx.rx_left_length = n /\
d1.ds_abs0_rx.rx_data_buffer = [] /\ n > 1 /\ l1' <> [] ==>
?n1 d0' d1'.
n_tau_tr n1 abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = x::l1' /\ 
d0'.ds_abs0_tx.tx_cur_length = 1 /\
d1'.state = abs0_rx_idle /\ d1'.ds_abs0_rx.rx_left_length = n - 1 /\
d1'.ds_abs0_rx.rx_data_buffer = [x]``,
rw [] >>
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, ds_abs0_tr_cases,
ABS0_RX_LBL_ENABLE_def, abs0_tx_op_value_def, abs0_tx_op_state_def,
abs0_tx_op_def, abs0_rx_op_def, abs0_rx_idle_op_def, 
ABS0_CALL_INIT_ENABLE_def, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def,
abs0_rx_update_tau_op_def, abs0_rx_reading_tau_op_def] >>
fs [] >> 
Q.EXISTS_TAC `d0 with  <|state := abs0_tx;
ds_abs0_tx := d0.ds_abs0_tx with tx_cur_length := 1|>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_idle;
ds_abs0_rx := d1.ds_abs0_rx with <|rx_data_buffer := [x];
rx_left_length := d1.ds_abs0_rx.rx_left_length − 1;
temp_RSR := x|> |>` >> 
rw []);

val abs0_tx_rx_internal_one_byte = store_thm("abs0_tx_rx_internal_one_byte",
``!x d0 d1 l1' l1 n.
d0.state = abs0_tx /\ d0.ds_abs0_tx.tx_data_buffer = l1 ++ [x] ++ l1' /\
d0.ds_abs0_tx.tx_cur_length = LENGTH l1 /\
d1.state = abs0_rx_idle /\ d1.ds_abs0_rx.rx_left_length = n - LENGTH l1 /\
d1.ds_abs0_rx.rx_data_buffer = l1 /\ n > LENGTH l1 /\ l1' <> [] /\ l1 <> [] ==>
?d0' d1'.
n_tau_tr 2 abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = l1 ++ [x] ++ l1' /\ 
d0'.ds_abs0_tx.tx_cur_length = LENGTH l1 + 1 /\
d1'.state = abs0_rx_idle /\ d1'.ds_abs0_rx.rx_left_length = n - (LENGTH l1 + 1) /\
d1'.ds_abs0_rx.rx_data_buffer = l1 ++ [x]``,
REPEAT STRIP_TAC >>
fs [n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, ds_abs0_tr_cases,
ABS0_RX_LBL_ENABLE_def, abs0_tx_op_value_def, abs0_tx_op_state_def,
abs0_tx_op_def, abs0_rx_op_def, abs0_rx_idle_op_def, ABS0_CALL_INIT_ENABLE_def,
ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_update_tau_op_def, 
abs0_rx_reading_tau_op_def, GSYM LEFT_EXISTS_AND_THM] >>
`EL (LENGTH l1) (l1 ++ [x] ++ l1') = x` by rw [el_append3] >>
Cases_on `LENGTH l1' > 0` >>
fs [] >-
(Q.EXISTS_TAC `d0 with <|state := abs0_tx;
ds_abs0_tx := d0.ds_abs0_tx with tx_cur_length := LENGTH l1 + 1|>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_idle;
ds_abs0_rx := d1.ds_abs0_rx with <|rx_data_buffer := l1 ⧺ [x];
rx_left_length := n − (LENGTH l1 + 1); temp_RSR := x|> |>` >>
rw []) >>
Cases_on `l1'` >>
fs []);

(* theorem 2-1, abs0 devices can transmit and receive data with a loop applying tx and rx mode repsectively *)
val abs0_tx_rx_data_loop_correct = store_thm("abs0_tx_rx_data_loop_correct",
``!l1 d0 d1 l1' n.
d0.state = abs0_tx /\ d0.ds_abs0_tx.tx_data_buffer = l1 ++ l1' /\
d0.ds_abs0_tx.tx_cur_length = 0 /\
d1.state = abs0_rx_idle /\ d1.ds_abs0_rx.rx_left_length = n /\
d1.ds_abs0_rx.rx_data_buffer = [] /\ n > LENGTH l1 /\ l1 <> [] /\ l1' <> [] ==>
?n1 d0' d1'.
n_tau_tr n1 abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = l1 ++ l1' /\ 
d0'.ds_abs0_tx.tx_cur_length = LENGTH l1 /\
d1'.state = abs0_rx_idle /\ d1'.ds_abs0_rx.rx_left_length = n - (LENGTH l1) /\
d1'.ds_abs0_rx.rx_data_buffer = l1``,
INDUCT_THEN SNOC_INDUCT STRIP_ASSUME_TAC >-
rw [] >>
REPEAT STRIP_TAC >>
Cases_on `l1 = []` >>
fs [] >- rw [abs0_tx_rx_first_one_byte] >>
`[x] ++ l1' <> []` by rw [] >>
`l1 ++ [x] ++ l1' = l1 ++ ([x] ++ l1')` by rw [] >>
`n > LENGTH l1` by rw [] >>
`?n1 d0'' d1''.
n_tau_tr n1 abs0_global_tr (d0,d1) tau (d0'',d1'') /\
d0''.state = abs0_tx /\
d0''.ds_abs0_tx.tx_data_buffer = l1 ⧺ ([x] ++ l1') /\
d0''.ds_abs0_tx.tx_cur_length = LENGTH l1 /\
d1''.state = abs0_rx_idle /\
d1''.ds_abs0_rx.rx_left_length = n − LENGTH l1 /\
d1''.ds_abs0_rx.rx_data_buffer = l1` by METIS_TAC [] >> fs [] >>
`?d0''' d1'''.
n_tau_tr 2 abs0_global_tr (d0'',d1'') tau (d0''',d1''') /\
d0'''.state = abs0_tx /\ d0'''.ds_abs0_tx.tx_data_buffer = l1 ++ [x] ++ l1' /\ 
d0'''.ds_abs0_tx.tx_cur_length = LENGTH l1 + 1 /\
d1'''.state = abs0_rx_idle /\ d1'''.ds_abs0_rx.rx_left_length = n - (LENGTH l1 + 1) /\
d1'''.ds_abs0_rx.rx_data_buffer = l1 ++ [x]` by fs [abs0_tx_rx_internal_one_byte] >>
Q.EXISTS_TAC `SUC (2 + n1)` >>
Q.EXISTS_TAC `d0'''` >>
Q.EXISTS_TAC `d1'''` >>
fs [] >>
`n1 + 2 = 2 + n1` by rw [] >>
METIS_TAC [n_tau_tr_plus]);

(* theorem 2-2, devices can reach a state that only the last one is going to transmit *)
val abs0_tx_rx_data_left_last_one = store_thm("abs0_tx_rx_data_left_last_one",
``!l1 d0 d1 a n.
d0.state = abs0_tx /\ d0.ds_abs0_tx.tx_data_buffer = l1 ++ [a] /\
d0.ds_abs0_tx.tx_cur_length = 0 /\
d1.state = abs0_rx_idle /\ d1.ds_abs0_rx.rx_left_length = n /\
d1.ds_abs0_rx.rx_data_buffer = [] /\ n > LENGTH l1 /\ l1 <> [] ==>
?n1 d0' d1'.
n_tau_tr n1 abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = l1 ++ [a] /\ 
d0'.ds_abs0_tx.tx_cur_length = LENGTH l1 /\
d1'.state = abs0_rx_idle /\ d1'.ds_abs0_rx.rx_left_length = n - (LENGTH l1) /\
d1'.ds_abs0_rx.rx_data_buffer = l1``,
rw [abs0_tx_rx_data_loop_correct]);

(* theorem 3-1, transmit and receive the last one byte *)
val abs0_tx_rx_finish_last_one = store_thm("abs0_tx_rx_finish_last_one",
``!l1 d0 d1 a n.
d0.state = abs0_tx /\ d0.ds_abs0_tx.tx_data_buffer = l1 ++ [a] /\
d0.ds_abs0_tx.tx_cur_length = LENGTH l1 /\
d1.state = abs0_rx_idle /\ d1.ds_abs0_rx.rx_left_length = n - LENGTH l1 /\
d1.ds_abs0_rx.rx_data_buffer = l1 /\ n > LENGTH l1 /\ l1 <> [] ==>
?d0' d1'.
n_tau_tr 2 abs0_global_tr (d0,d1) tau (d0',d1') /\
d1'.ds_abs0_rx.rx_data_buffer = l1 ++ [a]``,
REPEAT STRIP_TAC >>
fs [n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, ds_abs0_tr_cases,
ABS0_RX_LBL_ENABLE_def, abs0_tx_op_value_def, abs0_tx_op_state_def,
abs0_tx_op_def, abs0_rx_op_def, abs0_rx_idle_op_def, ABS0_CALL_INIT_ENABLE_def,
ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_update_tau_op_def, 
abs0_rx_reading_tau_op_def, GSYM LEFT_EXISTS_AND_THM] >>
`EL (LENGTH l1) (l1 ++ [a] ++ []) = a` by rw [el_append3] >>
fs [] >>
Q.EXISTS_TAC `d0 with <|state := abs0_ready;
ds_abs0_tx := d0.ds_abs0_tx with tx_cur_length := LENGTH l1 + 1|>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_idle;
ds_abs0_rx := d1.ds_abs0_rx with <|rx_data_buffer := l1 ⧺ [a];
rx_left_length := n − (LENGTH l1 + 1); temp_RSR := a|> |>` >>
Q.EXISTS_TAC  `(d0 with <|state := abs0_ready;
ds_abs0_tx := d0.ds_abs0_tx with tx_cur_length := LENGTH l1 + 1|>,
d1 with <|state := abs0_rx_reading;
ds_abs0_rx := d1.ds_abs0_rx with temp_RSR := a|>)` >>
rw []);

(* theorem 3-2, applying tx and rx modes to tranmit a singeton *)
val abs0_tx_rx_correct_single = store_thm("abs0_tx_rx_correct_single",
``!d0 d1 d0' d1' a.
d0.state = abs0_ready /\ d1.state = abs0_ready  ==> 
ds_abs0_tr d0 (call_tx [a]) d0' /\ ds_abs0_tr d1 (call_rx 1) d1' ==>
?d0'' d1''.
n_tau_tr 2 abs0_global_tr (d0', d1') tau (d0'', d1'') /\
d1''.ds_abs0_rx.rx_data_buffer = [a]``,
rw [ds_abs0_tr_cases, call_tx_ds_abs0_def, call_rx_ds_abs0_def, 
n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, 
ABS0_RX_LBL_ENABLE_def, abs0_tx_op_value_def, abs0_tx_op_state_def,
abs0_tx_op_def, abs0_rx_op_def, abs0_rx_idle_op_def, 
ABS0_CALL_INIT_ENABLE_def, ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def,
abs0_rx_update_tau_op_def, GSYM LEFT_EXISTS_AND_THM] >>
Q.EXISTS_TAC `d0 with <|state := abs0_ready;
ds_abs0_tx := <|tx_data_buffer := [a]; tx_cur_length := 1|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_idle;
ds_abs0_rx := d1.ds_abs0_rx with
<|rx_data_buffer := [a]; rx_left_length := 0;
temp_RSR := a|> |>` >>
Q.EXISTS_TAC `(d0 with <|state := abs0_ready;
ds_abs0_tx := <|tx_data_buffer := [a]; tx_cur_length := 1|> |>,
d1 with <|state := abs0_rx_reading;
ds_abs0_rx := d1.ds_abs0_rx with
<|rx_data_buffer := []; rx_left_length := 1; temp_RSR := a|> |>)` >>
rw [abs0_rx_reading_tau_op_def]);

(* abs0 tx and rx modes are correct: 
   if two devices apply tx and rx mode respectively, 
   the data buffer can be transmitted from d0 to d1 *)
val abs0_tx_rx_correct = store_thm ("abs0_tx_rx_correct",
``!d0 d1 d0' d1' l n.
d0.state = abs0_ready /\ d1.state = abs0_ready  ==> 
ds_abs0_tr d0 (call_tx l) d0' /\ ds_abs0_tr d1 (call_rx n) d1' /\ l <> [] /\ n = LENGTH l ==>
?n' d0'' d1''.
n_tau_tr n' abs0_global_tr (d0', d1') tau (d0'', d1'') /\
d1''.ds_abs0_rx.rx_data_buffer = l``,
rw [] >> Cases_on `l` >> fs [] >>
`t = [] \/ ?x l'. t = SNOC x l'` by rw [SNOC_CASES] >-
(fs [] >> METIS_TAC [abs0_tx_rx_correct_single]) >>
fs [SNOC_APPEND] >>
`ds_abs0_tr d0 (call_tx (h::l'++[x])) d0'` by fs [] >>
`h::l' ++ [x] <> []` by rw [] >>
`SUC (LENGTH l' + 1) > 0` by rw [] >>
`d0'.state = abs0_tx /\ d0'.ds_abs0_tx.tx_data_buffer = h::l'++[x] /\
d0'.ds_abs0_tx.tx_cur_length = 0 /\
d1'.state = abs0_rx_idle /\ 
d1'.ds_abs0_rx.rx_left_length = SUC (LENGTH l' + 1) /\
d1'.ds_abs0_rx.rx_data_buffer = []` by METIS_TAC [abs0_tx_rx_calls_correct] >>
`SUC (LENGTH l' + 1) > LENGTH (h::l')` by rw [] >>
`h::l' <> []` by rw [] >>
`?n1 d0'' d1''.
n_tau_tr n1 abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.state = abs0_tx /\ d0''.ds_abs0_tx.tx_data_buffer = h::l'++[x] /\ 
d0''.ds_abs0_tx.tx_cur_length = LENGTH (h::l') /\
d1''.state = abs0_rx_idle /\ 
d1''.ds_abs0_rx.rx_left_length = (SUC (LENGTH l' + 1)) - (LENGTH (h::l')) /\
d1''.ds_abs0_rx.rx_data_buffer = h::l'` by METIS_TAC [abs0_tx_rx_data_left_last_one] >>
`?d0''' d1'''.
n_tau_tr 2 abs0_global_tr (d0'',d1'') tau (d0''',d1''') /\
d1'''.ds_abs0_rx.rx_data_buffer = h::l' ++ [x]` by METIS_TAC [abs0_tx_rx_finish_last_one] >>
Q.EXISTS_TAC `SUC (2 + n1)` >>
Q.EXISTS_TAC `d0'''` >>
Q.EXISTS_TAC `d1'''` >>
fs [] >>
`n1 + 2 = 2 + n1` by rw [] >>
METIS_TAC [n_tau_tr_plus]);

val _ = export_theory();
