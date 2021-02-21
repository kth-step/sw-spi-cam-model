open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory ds_abs0_txTheory ds_abs0_rxTheory ds_abs0_tauTheory ds_abs0_relTheory;

val _ = new_theory "tx_rx_correct";

val (abs0_global_tr_rules, abs0_global_tr_ind, abs0_global_tr_cases) = Hol_reln `
(!d0 d1 d0'. ds_abs0_tr d0 call_init d0' ==>
abs0_global_tr (d0, d1) (d0', d1)) /\
(!d0 d1 d1'. ds_abs0_tr d1 call_init d1' ==>
abs0_global_tr (d0, d1) (d0, d1')) /\
(!d0 d1 d0' buffer. ds_abs0_tr d0 (call_tx buffer) d0' ==>
abs0_global_tr (d0, d1) (d0', d1)) /\
(!d0 d1 d1' buffer. ds_abs0_tr d1 (call_tx buffer) d1' ==>
abs0_global_tr (d0, d1) (d0, d1')) /\
(!d0 d1 d0' l. ds_abs0_tr d0 (call_rx l) d0' ==>
abs0_global_tr (d0, d1) (d0', d1)) /\
(!d0 d1 d1' l. ds_abs0_tr d1 (call_rx l) d1' ==>
abs0_global_tr (d0, d1) (d0, d1')) /\
(!d0 d1 buffer0 buffer1 d0' d1'. 
ds_abs0_tr d0 (call_xfer buffer0) d0' /\ ds_abs0_tr d1 (call_xfer buffer1) d1' /\
LENGTH buffer0 = LENGTH buffer1 ==>
abs0_global_tr (d0, d1) (d0', d1')) /\
(!d0 d1 d0'. ds_abs0_tr d0 tau d0' ==>
abs0_global_tr (d0, d1) (d0', d1)) /\
(!d0 d1 d1'. ds_abs0_tr d1 tau d1' ==>
abs0_global_tr (d0, d1) (d0, d1')) /\
(!d0 d1 data d0' d1'. ds_abs0_tr d0 (TX data) d0' /\ ds_abs0_tr d1 (RX data) d1' ==>
abs0_global_tr (d0, d1) (d0', d1')) /\
(!d0 d1 data d0' d1'. ds_abs0_tr d0 (RX data) d0' /\ ds_abs0_tr d1 (TX data) d1' ==>
abs0_global_tr (d0, d1) (d0', d1')) /\
(!d0 d1 dataI dataO d0' d1'. 
ds_abs0_tr d0 (XFER dataI dataO) d0' /\ ds_abs0_tr d1 (XFER dataO dataI) d1' ==>
abs0_global_tr (d0, d1) (d0', d1'))`

(* SPI device 0 and 1 apply tx and rx modes to transmit one byte a *)
val abs0_tx_rx_correct_single = store_thm("abs0_tx_rx_correct_single",
``!d0 d1 a.
d0.state = abs0_ready /\ d1.state = abs0_ready  ==> 
?d0' d1' d0'' d1'' d0''' d1''' d0'''' d1''''. 
ds_abs0_tr d0 (call_tx [a]) d0' /\ ds_abs0_tr d1 (call_rx 1) d1' /\
abs0_global_tr (d0', d1') (d0'', d1'') /\ abs0_global_tr (d0'', d1'') (d0''', d1''') /\
abs0_global_tr (d0''', d1''') (d0'''',d1'''') /\
d1''''.ds_abs0_rx.rx_data_buffer = [a]``,
rw [ds_abs0_tr_cases, call_tx_ds_abs0_def, call_rx_ds_abs0_def, abs0_global_tr_cases, 
ABS0_RX_LBL_ENABLE_def, abs0_tx_op_value_def, abs0_tx_op_state_def,
abs0_tx_op_def, abs0_rx_op_def, abs0_rx_idle_op_def] >>
Q.EXISTS_TAC `d0 with <|state := abs0_ready;
ds_abs0_tx := <|tx_data_buffer := [a]; tx_cur_length := 1|> |>` >>
Q.EXISTS_TAC  `d1 with <|state := abs0_rx_update;
ds_abs0_rx := d1.ds_abs0_rx with
<|rx_data_buffer := []; rx_left_length := 1; temp_RSR := a|> |>` >>
rw [ABS0_TAU_LBL_ENABLE_def, abs0_tau_op_def, abs0_rx_update_tau_op_def] >>
Q.EXISTS_TAC `d0 with <|state := abs0_ready;
ds_abs0_tx := <|tx_data_buffer := [a]; tx_cur_length := 1|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_reading;
ds_abs0_rx := d1.ds_abs0_rx with
<|rx_data_buffer := []; rx_left_length := 1; temp_RSR := a|> |>` >>
rw [abs0_rx_reading_tau_op_def] >>
Q.EXISTS_TAC `d0 with <|state := abs0_ready;
ds_abs0_tx := <|tx_data_buffer := [a]; tx_cur_length := 1|> |>` >>
Q.EXISTS_TAC `d1 with <|state := abs0_rx_idle;
ds_abs0_rx := d1.ds_abs0_rx with
<|rx_data_buffer := [a]; rx_left_length := 0;
temp_RSR := a|> |>` >>
rw []);

val _ = export_theory();
