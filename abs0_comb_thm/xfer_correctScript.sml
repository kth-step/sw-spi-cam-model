open HolKernel bossLib boolLib Parse listTheory;
open ds_abs0_stateTheory ds_abs0_xferTheory ds_abs0_tauTheory ds_abs0_initTheory ds_abs0_relTheory weak_bisimulationTheory abs0_comb_weak_bisimulationTheory;

val _ = new_theory "xfer_correct";

(* abs0 xfer mode correctness theorem 1: from ready state, abs0 can apply xfer mode *)
val abs0_xfer_call_xfer_correct = store_thm("abs0_xfer_call_xfer_correct",
``!d0 d1 l1 l2 d0' d1'.
d0.state = abs0_ready /\ d1.state = abs0_ready /\ LENGTH l1 = LENGTH l2 /\
l1 <> [] /\ l2 <> [] ==>
ds_abs0_tr d0 (call_xfer l1) d0' /\ ds_abs0_tr d1 (call_xfer l2) d1' ==>
d0'.state = abs0_xfer_idle /\ d0'.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0'.ds_abs0_xfer.xfer_dataOUT_buffer = l1 /\ d0'.ds_abs0_xfer.xfer_cur_length = 0 /\
d1'.state = abs0_xfer_idle /\ d1'.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1'.ds_abs0_xfer.xfer_dataOUT_buffer = l2 /\ d1'.ds_abs0_xfer.xfer_cur_length = 0``,
rw [ds_abs0_tr_cases, call_xfer_ds_abs0_def]);

(* lemmas for abs0 xfer correctness theorem 2 *)
val abs0_xfer_idle_first_one_byte = store_thm("abs0_xfer_idle_first_one_byte",
``!d0 d1 x x' l1' l2'.
d0.state = abs0_xfer_idle /\ 
d0.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0.ds_abs0_xfer.xfer_dataOUT_buffer = x::l1' /\
d0.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0.ds_abs0_xfer.xfer_cur_length = 0 /\
d1.state = abs0_xfer_idle /\ 
d1.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1.ds_abs0_xfer.xfer_dataOUT_buffer = x'::l2' /\
d1.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1.ds_abs0_xfer.xfer_cur_length = 0 /\
l1' <> [] /\ l2' <> [] ==> 
?n d0'' d1''.
n_tau_tr n abs0_global_tr (d0,d1) tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = [x'] /\ d0''.state = abs0_xfer_idle /\
d0''.ds_abs0_xfer.xfer_dataOUT_buffer = x::l1' /\
d0''.ds_abs0_xfer.xfer_cur_length = 1 /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = [x] /\ d1''.state = abs0_xfer_idle /\
d1''.ds_abs0_xfer.xfer_dataOUT_buffer = x'::l2' /\
d1''.ds_abs0_xfer.xfer_cur_length = 1``,
rw [] >>
`LENGTH l1' > 0 /\ LENGTH l2' > 0` by fs [NOT_NIL_EQ_LENGTH_NOT_0] >>
Q.EXISTS_TAC `SUC 1` >>
Q.EXISTS_TAC `d0 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d0.ds_abs0_xfer with <|xfer_dataIN_buffer := [x']; 
xfer_cur_length := 1; xfer_RSR := x'|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d1.ds_abs0_xfer with <|xfer_dataIN_buffer := [x];
xfer_cur_length := 1; xfer_RSR := x|> |>` >>
rw [n_tau_tr_def, n_tau_tr_SUC, GSYM LEFT_EXISTS_AND_THM, abs0_global_tr_cases, ds_abs0_tr_cases, abs0_xfer_op_state_def, abs0_xfer_op_value_def, abs0_xfer_op_def] >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_done;
ds_abs0_xfer := d0.ds_abs0_xfer with
<|xfer_cur_length := 1; xfer_RSR := x'|> |>,
d1 with <|state := abs0_xfer_done;
ds_abs0_xfer := d1.ds_abs0_xfer with
<|xfer_cur_length := 1; xfer_RSR := x|> |>)` >>
rw [abs0_tau_op_def, abs0_xfer_tau_op_def, ABS0_TAU_LBL_ENABLE_def, ABS0_CALL_INIT_ENABLE_def] >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d0.ds_abs0_xfer with <|xfer_dataIN_buffer := [x'];
xfer_cur_length := 1; xfer_RSR := x'|> |>,
d1 with <|state := abs0_xfer_done; 
ds_abs0_xfer := d1.ds_abs0_xfer with
<|xfer_cur_length := 1; xfer_RSR := x|> |>)` >>
rw []);

val abs0_xfer_idle_internal_one_byte = store_thm("abs0_xfer_idle_internal_one_byte",
``!d0 d1 l1 l2 l1' l2' x x'.
d0.state = abs0_xfer_idle /\
d0.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\
d0.ds_abs0_xfer.xfer_cur_length = LENGTH l1 /\
d0.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ [x] ++ l1' /\ 
d1.state = abs0_xfer_idle /\
d1.ds_abs0_xfer.xfer_dataIN_buffer = l1 /\
d1.ds_abs0_xfer.xfer_cur_length = LENGTH l2 /\
d1.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ [x'] ++ l2' /\
l1' <> [] /\ l2' <> [] ==>
?d0' d1'. n_tau_tr 2 abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.ds_abs0_xfer.xfer_dataIN_buffer = l2 ++ [x'] /\ d0'.state = abs0_xfer_idle /\
d0'.ds_abs0_xfer.xfer_cur_length = SUC (LENGTH l1) /\
d0'.ds_abs0_xfer.xfer_dataOUT_buffer =  l1 ++ [x] ++ l1' /\
d1'.ds_abs0_xfer.xfer_dataIN_buffer = l1 ++ [x] /\ d1'.state = abs0_xfer_idle /\
d1'.ds_abs0_xfer.xfer_cur_length = SUC (LENGTH l2) /\
d1'.ds_abs0_xfer.xfer_dataOUT_buffer =  l2 ++ [x'] ++ l2'``,
REPEAT STRIP_TAC >>
`LENGTH l1' > 0 /\ LENGTH l2' > 0` by fs [NOT_NIL_EQ_LENGTH_NOT_0] >>
Q.EXISTS_TAC `d0 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d0.ds_abs0_xfer with <|xfer_dataIN_buffer := l2 ++ [x']; 
xfer_cur_length := SUC (LENGTH l1); xfer_RSR := x'|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d1.ds_abs0_xfer with <|xfer_dataIN_buffer := l1 ++ [x];
xfer_cur_length := SUC (LENGTH l2); xfer_RSR := x|> |>` >>
fs [n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, abs0_global_tr_cases, ds_abs0_tr_cases, abs0_xfer_op_state_def, abs0_xfer_op_value_def, abs0_xfer_op_def] >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_done;
ds_abs0_xfer := d0.ds_abs0_xfer with
<|xfer_cur_length := LENGTH l1 + 1; xfer_RSR := EL (LENGTH l2) (l2 ⧺ [x'] ⧺ l2')|> |>,
d1 with <|state := abs0_xfer_done; ds_abs0_xfer :=
d1.ds_abs0_xfer with <|xfer_cur_length := LENGTH l2 + 1;
xfer_RSR := EL (LENGTH l1) (l1 ⧺ [x] ⧺ l1')|> |>)` >>
fs [abs0_tau_op_def, abs0_xfer_tau_op_def, ABS0_TAU_LBL_ENABLE_def, ABS0_CALL_INIT_ENABLE_def, el_append3] >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_idle;
ds_abs0_xfer := d0.ds_abs0_xfer with
<|xfer_dataIN_buffer := l2 ⧺ [x'];
xfer_cur_length := LENGTH l1 + 1;
xfer_RSR := x'|> |>,
d1 with <|state := abs0_xfer_done;
ds_abs0_xfer := d1.ds_abs0_xfer with
<|xfer_cur_length := LENGTH l2 + 1;
xfer_RSR := x|> |>)` >>
`LENGTH l1 + 1 = SUC (LENGTH l1) /\
 LENGTH l2 + 1 = SUC (LENGTH l2)` by rw [] >>
rw []);

(* abs0 xfer correctness theorem 2_1: abs0 can exchange data between devices with a loop *)
val abs0_xfer_idle_exchange_data_correct = store_thm("abs0_xfer_idle_exchange_data_correct",
``!l1 l2 d0 d1 l1' l2'.
d0.state = abs0_xfer_idle /\ d0.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ l1' /\ d0.ds_abs0_xfer.xfer_cur_length = 0 /\
d1.state = abs0_xfer_idle /\ d1.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ l2' /\ d1.ds_abs0_xfer.xfer_cur_length = 0 /\ LENGTH l1 = LENGTH l2 /\
l1 <> [] /\ l2 <> [] /\ l1' <> [] /\ l2' <> [] ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0,d1) tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\ d0''.state = abs0_xfer_idle /\
d0''.ds_abs0_xfer.xfer_cur_length = LENGTH l1 /\
d0''.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ l1' /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = l1 /\ d1''.state = abs0_xfer_idle /\
d1''.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ l2' /\
d1''.ds_abs0_xfer.xfer_cur_length  = LENGTH l2``,
INDUCT_THEN SNOC_INDUCT STRIP_ASSUME_TAC >- (rw []) >>
GEN_TAC >> INDUCT_THEN SNOC_INDUCT STRIP_ASSUME_TAC >> rw [] >>
Cases_on `l1 = []` >- 
(`l2 = []` by fs [] >> fs [] >>
METIS_TAC [abs0_xfer_idle_first_one_byte]) >>
Cases_on `l2 = []` >> fs [] >>
`[x] ++ l1' <> [] /\ [x'] ++ l2' <> []` by rw [] >>
`LENGTH l2 = LENGTH l2` by rw [] >>
`l1 ++ [x] ++ l1' = l1 ++ ([x] ++ l1') /\
 l2 ++ [x'] ++ l2' = l2 ++ ([x'] ++ l2')` by rw [] >>
`?n d0'' d1''.
n_tau_tr n abs0_global_tr (d0,d1) tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\
d0''.state = abs0_xfer_idle /\
d0''.ds_abs0_xfer.xfer_cur_length = LENGTH l1 /\
d0''.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ ([x] ++ l1') /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = l1 /\
d1''.state = abs0_xfer_idle /\
d1''.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ ([x'] ++ l2') /\
d1''.ds_abs0_xfer.xfer_cur_length = LENGTH l2` by METIS_TAC [] >> fs [] >>
`?d0''' d1'''. 
n_tau_tr 2 abs0_global_tr (d0'',d1'') tau (d0''',d1''') /\
d0'''.ds_abs0_xfer.xfer_dataIN_buffer = l2 ++ [x'] /\ d0'''.state = abs0_xfer_idle /\
d0'''.ds_abs0_xfer.xfer_cur_length = SUC (LENGTH l1) /\
d0'''.ds_abs0_xfer.xfer_dataOUT_buffer =  l1 ++ [x] ++ l1' /\
d1'''.ds_abs0_xfer.xfer_dataIN_buffer = l1 ++ [x] /\ d1'''.state = abs0_xfer_idle /\
d1'''.ds_abs0_xfer.xfer_cur_length = SUC (LENGTH l2) /\
d1'''.ds_abs0_xfer.xfer_dataOUT_buffer =  l2 ++ [x'] ++ l2'` by fs [abs0_xfer_idle_internal_one_byte] >>
Q.EXISTS_TAC `SUC (2 + n)` >>
Q.EXISTS_TAC `d0'''` >>
Q.EXISTS_TAC `d1'''` >>
METIS_TAC [n_tau_tr_plus]);

(* theorem 2_2, for any initial xfer state, it can reach a state that 
   only the last one byte is going to transmit *)
val abs0_xfer_idle_last_one_correct = store_thm("abs0_xfer_idle_last_one_correct",
``!l1 l2 d0 d1 h h'.
d0.state = abs0_xfer_idle /\ d0.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ [h] /\ d0.ds_abs0_xfer.xfer_cur_length = 0 /\
d1.state = abs0_xfer_idle /\ d1.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ [h'] /\ d1.ds_abs0_xfer.xfer_cur_length = 0 /\ 
LENGTH l1 = LENGTH l2 /\ l1 <> [] /\ l2 <> [] ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0,d1) tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\ d0''.state = abs0_xfer_idle /\
d0''.ds_abs0_xfer.xfer_cur_length = LENGTH l1 /\
d0''.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ [h] /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = l1 /\ d1''.state = abs0_xfer_idle /\
d1''.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ [h'] /\
d1''.ds_abs0_xfer.xfer_cur_length  = LENGTH l2``,
rw [abs0_xfer_idle_exchange_data_correct]);

(* theorem 3_1, transfer the last one byte *)
val abs0_xfer_finish_last_one = store_thm("abs0_xfer_finish_last_one",
``!l1 l2 d0 d1 h h'.
d0.state = abs0_xfer_idle /\ d0.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\
d0.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ [h] /\ d0.ds_abs0_xfer.xfer_cur_length = LENGTH l1 /\
d1.state = abs0_xfer_idle /\ d1.ds_abs0_xfer.xfer_dataIN_buffer = l1 /\
d1.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ [h'] /\ d1.ds_abs0_xfer.xfer_cur_length = LENGTH l2 /\ 
LENGTH l1 = LENGTH l2 /\ l1 <> [] /\ l2 <> [] ==>
?d0' d1'. n_tau_tr (SUC 1) abs0_global_tr (d0,d1) tau (d0',d1') /\
d0'.ds_abs0_xfer.xfer_dataIN_buffer = l2 ++ [h'] /\ d0'.state = abs0_xfer_reply /\
d0'.ds_abs0_xfer.xfer_cur_length = LENGTH l1 + 1 /\
d0'.ds_abs0_xfer.xfer_dataOUT_buffer = l1 ++ [h] /\
d1'.ds_abs0_xfer.xfer_dataIN_buffer = l1 ++ [h] /\ d1'.state = abs0_xfer_reply /\
d1'.ds_abs0_xfer.xfer_dataOUT_buffer = l2 ++ [h'] /\
d1'.ds_abs0_xfer.xfer_cur_length  = LENGTH l2 + 1``,
REPEAT STRIP_TAC >>
fs [n_tau_tr_def, n_tau_tr_SUC, abs0_global_tr_cases, ds_abs0_tr_cases, 
ABS0_CALL_INIT_ENABLE_def, ABS0_TAU_LBL_ENABLE_def, abs0_xfer_op_value_def, 
abs0_xfer_op_state_def, abs0_xfer_op_def, GSYM LEFT_EXISTS_AND_THM] >>
`EL (LENGTH l2) (l2 ++ [h'] ++ []) = h' /\
 EL (LENGTH l1) (l1 ++ [h] ++ []) = h`by rw [el_append3] >>
fs [] >>
`EL (LENGTH l2) (l1 ++ [h]) = h` by METIS_TAC [] >>
fs [abs0_tau_op_def, abs0_xfer_tau_op_def] >>
Q.EXISTS_TAC `d0 with <|state := abs0_xfer_reply;
ds_abs0_xfer := d0.ds_abs0_xfer with
<|xfer_dataIN_buffer := l2 ++ [h'];
xfer_cur_length := LENGTH l2 + 1; xfer_RSR := h'|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_xfer_reply;
ds_abs0_xfer := d1.ds_abs0_xfer with
<|xfer_dataIN_buffer := l1 ++ [h];
xfer_cur_length := LENGTH l2 + 1;
xfer_RSR := h|> |>` >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_reply;
ds_abs0_xfer := d0.ds_abs0_xfer with
<|xfer_dataIN_buffer := l2 ++ [h'];
xfer_cur_length := LENGTH l2 + 1; xfer_RSR := h'|> |>,
d1 with <|state := abs0_xfer_done;
ds_abs0_xfer := d1.ds_abs0_xfer with 
<|xfer_cur_length := LENGTH l2 + 1; xfer_RSR := h|> |>)` >>
fs []);

(* theorem 3_2, transfer a buffer that is a singleton *)
val abs0_xfer_singleton_correct = store_thm("abs0_xfer_singleton_correct",
``!d0 d1 d0' d1' a b.
d0.state = abs0_ready /\ d1.state = abs0_ready ==> 
ds_abs0_tr d0 (call_xfer [a]) d0' /\
ds_abs0_tr d1 (call_xfer [b]) d1' ==>
?d0'' d1''. n_tau_tr (SUC 1) abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = [b] /\ d0''.state = abs0_xfer_reply /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = [a] /\ d1''.state = abs0_xfer_reply``,
rw [ds_abs0_tr_cases, call_xfer_ds_abs0_def, n_tau_tr_def, n_tau_tr_SUC,
abs0_global_tr_cases, ABS0_CALL_INIT_ENABLE_def, ABS0_TAU_LBL_ENABLE_def,
abs0_xfer_op_state_def, abs0_xfer_op_value_def, abs0_xfer_op_def, 
abs0_tau_op_def, abs0_xfer_tau_op_def, GSYM LEFT_EXISTS_AND_THM] >>
Q.EXISTS_TAC `d0 with <|state := abs0_xfer_reply;
ds_abs0_xfer := <|xfer_dataIN_buffer := [b]; xfer_dataOUT_buffer := [a];
xfer_cur_length := 1; xfer_RSR := b|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_xfer_reply;
ds_abs0_xfer := <|xfer_dataIN_buffer := [a]; xfer_dataOUT_buffer := [b];
xfer_cur_length := 1; xfer_RSR := a|> |>` >>
Q.EXISTS_TAC `(d0 with <|state := abs0_xfer_reply;
ds_abs0_xfer := <|xfer_dataIN_buffer := [b]; xfer_dataOUT_buffer := [a];
xfer_cur_length := 1; xfer_RSR := b|> |>,
d1 with <|state := abs0_xfer_done;
ds_abs0_xfer := <|xfer_dataIN_buffer := []; xfer_dataOUT_buffer := [b];
xfer_cur_length := 1; xfer_RSR := a|> |>)` >>
rw []);
 
(* abs0 xfer mode is correct: 
   if two devices are called with xfer mode,
   the data buffer will be received by another device *)
val abs0_xfer_correct = store_thm("abs0_xfer_correct",
``!d0 d1 l1 l2 d0' d1'.
d0.state = abs0_ready /\ d1.state = abs0_ready /\ 
LENGTH l1 = LENGTH l2 /\ l1 <> [] /\ l2 <> [] ==>
ds_abs0_tr d0 (call_xfer l1) d0' /\
ds_abs0_tr d1 (call_xfer l2) d1' ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = l2 /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = l1``,
rw [] >> Cases_on `l1` >> Cases_on `l2` >> fs [] >>
`t = [] \/ ?x l'. t = SNOC x l'` by rw [SNOC_CASES] >-
(`t' = []` by fs [] >> fs [] >>
METIS_TAC [abs0_xfer_singleton_correct]) >>
`t' = [] \/ ?x' l''. t' = SNOC x' l''`by rw [SNOC_CASES] >>
fs [SNOC_APPEND] >>
`ds_abs0_tr d0 (call_xfer (h::l'++[x])) d0' /\
ds_abs0_tr d1 (call_xfer (h'::l''++[x'])) d1'` by fs [] >>
`LENGTH (h::l' ++ [x]) = LENGTH (h'::l'' ++ [x'])` by rw [] >>
`h::l' ++ [x] <> [] /\ h'::l'' ++ [x'] <> []` by rw [] >>
`d0'.state = abs0_xfer_idle /\ d0'.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d0'.ds_abs0_xfer.xfer_dataOUT_buffer = h::l' ++ [x] /\ d0'.ds_abs0_xfer.xfer_cur_length = 0 /\
d1'.state = abs0_xfer_idle /\ d1'.ds_abs0_xfer.xfer_dataIN_buffer = [] /\
d1'.ds_abs0_xfer.xfer_dataOUT_buffer = h'::l'' ++ [x'] /\ d1'.ds_abs0_xfer.xfer_cur_length = 0` by METIS_TAC [abs0_xfer_call_xfer_correct] >>
`LENGTH (h::l') = LENGTH (h'::l'')` by rw [] >>
`h::l' <> [] /\ h'::l'' <> []` by rw [] >>
`?n1 d0'' d1''. n_tau_tr n1 abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = h'::l'' /\ d0''.state = abs0_xfer_idle /\
d0''.ds_abs0_xfer.xfer_cur_length = LENGTH (h::l') /\
d0''.ds_abs0_xfer.xfer_dataOUT_buffer = h::l' ++ [x] /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = h::l' /\ d1''.state = abs0_xfer_idle /\
d1''.ds_abs0_xfer.xfer_dataOUT_buffer = h'::l'' ++ [x'] /\
d1''.ds_abs0_xfer.xfer_cur_length  = LENGTH (h'::l'')` by METIS_TAC [abs0_xfer_idle_last_one_correct] >>
`?d0''' d1'''. n_tau_tr (SUC 1) abs0_global_tr (d0'',d1'') tau (d0''',d1''') /\
d0'''.ds_abs0_xfer.xfer_dataIN_buffer =  h'::l'' ++ [x'] /\ 
d0'''.state = abs0_xfer_reply /\
d0'''.ds_abs0_xfer.xfer_cur_length = LENGTH (h::l') + 1 /\
d0'''.ds_abs0_xfer.xfer_dataOUT_buffer = h::l' ++ [x] /\
d1'''.ds_abs0_xfer.xfer_dataIN_buffer = h::l' ++ [x] /\ 
d1'''.state = abs0_xfer_reply /\
d1'''.ds_abs0_xfer.xfer_dataOUT_buffer = h'::l'' ++ [x'] /\
d1'''.ds_abs0_xfer.xfer_cur_length  = LENGTH (h'::l'') + 1` by METIS_TAC [abs0_xfer_finish_last_one] >>
fs [] >>
Q.EXISTS_TAC `SUC (2 + n1)` >>
Q.EXISTS_TAC `d0'''` >>
Q.EXISTS_TAC `d1'''` >>
METIS_TAC [n_tau_tr_plus]);

val _ = export_theory();
