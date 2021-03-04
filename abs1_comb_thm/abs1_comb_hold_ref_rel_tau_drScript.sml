open HolKernel bossLib boolLib Parse wordsLib optionTheory;
open SPI_stateTheory SPI_relationTheory SPI_tauTheory SPI_return_regsTheory weak_bisimulationTheory driver_stateTheory driver_relationTheory driver_checkTheory driver_readTheory driver_writeTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_tau_dr";

(* related to rx automaton *)
(* ref_rel holds if ds_abs1 has tau_dr transition and ds_abs1.state = abs1_rx_ready *)
val ref_rel_holds_tau_dr_abs1_rx_ready = store_thm("ref_rel_holds_tau_dr_abs1_rx_ready",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_ready) /\ 
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi')) \/
(?n dr' spi'. n_tau_tr n local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi'))``,
rw [driver_abs1_rx_operations_def] >>
`dr.dr_rx.rx_left_length = ds_abs1.ds_abs1_rx.rx_left_length` by fs [ref_rel_def] >>
`(dr.state = dr_rx_check_rxs /\ spi.state = rx_data_ready) \/
(dr.state = dr_rx_read_rxs /\ spi.state = rx_data_ready)` by fs [IS_STATE_REL_def] >|
[(* dr_rx_check_rxs and rx_data_ready *)
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(0 >< 0) v:word1 = 1w` >|
[(* the stored value of rxs is 1w *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, DR_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr_check dr SPI0_CH0STAT (THE dr.dr_last_read_v)` >> 
Q.EXISTS_TAC `spi` >>
rw [dr_check_def, dr_check_rx_ch0stat_def, driver_abs1_rx_ready_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def], 
(* the stored value of rxs is 0w *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_rx_read_rxs` 
by rw [dr_check_def, dr_check_rx_ch0stat_def] >>
rw [] >>
`dr_read (dr with state := dr_rx_read_rxs) = dr with <| state := dr_rx_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
Q.EXISTS_TAC `dr_check (dr with <| state := dr_rx_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (read_SPI_regs_value SPI0_CH0STAT spi) |>) 
SPI0_CH0STAT (read_SPI_regs_value SPI0_CH0STAT spi)` >>
Q.EXISTS_TAC `read_SPI_regs_state SPI0_CH0STAT spi` >>
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >>
rw [dr_check_def, dr_check_rx_ch0stat_def, build_CH0STAT_def, SPI0_CH0STAT_def, 
driver_abs1_rx_ready_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []],
(* dr_rx_read_rxs and rx_data_ready *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_rx_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
Q.EXISTS_TAC `dr_check (dr with <| state := dr_rx_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (read_SPI_regs_value SPI0_CH0STAT spi) |>) 
SPI0_CH0STAT (read_SPI_regs_value SPI0_CH0STAT spi)` >>
Q.EXISTS_TAC `read_SPI_regs_state SPI0_CH0STAT spi` >>
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >>
rw [dr_check_def, dr_check_rx_ch0stat_def, build_CH0STAT_def, SPI0_CH0STAT_def, 
driver_abs1_rx_ready_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []]);

(* ref_rel holds if ds_abs1 has tau_dr transition and ds_abs1.state = abs1_rx_fetch_data *)
val ref_rel_holds_tau_dr_abs1_rx_fetch_data = store_thm("ref_rel_holds_tau_dr_abs1_rx_fetch_data",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_fetch_data) /\ 
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi')``,
rw [driver_abs1_rx_operations_def, driver_abs1_rx_fetch_data_op_def] >>
`dr.state = dr_rx_fetch_data /\ spi.state = rx_receive_data` by fs [IS_STATE_REL_def] >>
`dr.dr_last_read_ad = SOME SPI0_RX0 /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
rw [local_tr_cases, driver_tr_cases, DR_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr_check dr SPI0_RX0 (THE dr.dr_last_read_v)` >> 
Q.EXISTS_TAC `spi` >>
rw [dr_check_def, dr_check_rx0_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 has tau_dr transition and ds_abs1.state = abs1_rx_next *)
val ref_rel_holds_tau_dr_abs1_rx_next = store_thm("ref_rel_holds_tau_dr_abs1_rx_next",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_next) /\ 
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi')``,
rw [driver_abs1_rx_operations_def, driver_abs1_rx_next_op_def] >>
`dr.state = dr_rx_fetch_data /\ spi.state = rx_update_RX0` by fs [IS_STATE_REL_def] >>
`dr.dr_last_read_ad = SOME SPI0_RX0 /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
rw [local_tr_cases, driver_tr_cases, DR_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr_check dr SPI0_RX0 (THE dr.dr_last_read_v)` >> 
Q.EXISTS_TAC `spi` >>
rw [dr_check_def, dr_check_rx0_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 has tau_dr transition and ds_abs1.state = abs1_rx_next_ready *)
val ref_rel_holds_tau_dr_abs1_rx_next_ready = store_thm("ref_rel_holds_tau_dr_abs1_rx_next_ready",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_next_ready) /\ 
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi')``,
rw [driver_abs1_rx_operations_def, driver_abs1_rx_next_ready_op_def] >>
`dr.state = dr_rx_fetch_data /\ spi.state = rx_data_ready` by fs [IS_STATE_REL_def] >>
`dr.dr_last_read_ad = SOME SPI0_RX0 /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
rw [local_tr_cases, driver_tr_cases, DR_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr_check dr SPI0_RX0 (THE dr.dr_last_read_v)` >> 
Q.EXISTS_TAC `spi` >>
rw [dr_check_def, dr_check_rx0_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for rx *)
val abs1_comb_hold_ref_rel_tau_dr_rx = 
store_thm("abs1_comb_hold_ref_rel_tau_dr_rx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (DRIVER_ABS1_RX_ENABLE ds_abs1) ==>
(?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi')) \/
(?n dr' spi'. n_tau_tr n local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_rx_operations ds_abs1) (dr',spi'))``,
rw [DRIVER_ABS1_RX_ENABLE_def] >> 
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_dr_abs1_rx_ready, ref_rel_holds_tau_dr_abs1_rx_fetch_data,
ref_rel_holds_tau_dr_abs1_rx_next, ref_rel_holds_tau_dr_abs1_rx_next_ready]);


(* related to xfer automaton *)
(* (dr',spi') exists for xfer *)
val abs1_comb_hold_ref_rel_tau_dr_xfer = 
store_thm("abs1_comb_hold_ref_rel_tau_dr_xfer",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (DRIVER_ABS1_XFER_ENABLE ds_abs1) ==>
?dr' spi'. local_tr (dr,spi) tau (dr',spi') /\
ref_rel (driver_abs1_xfer_operations ds_abs1) (dr',spi')``,
rw [DRIVER_ABS1_XFER_ENABLE_def, driver_abs1_xfer_operations_def,
driver_abs1_xfer_fetch_data_op_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
`dr.state = dr_xfer_fetch_dataI /\ spi.state = xfer_ready_for_trans` by fs [IS_STATE_REL_def] >>
`dr.dr_last_read_ad = SOME SPI0_RX0 /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
rw [local_tr_cases, driver_tr_cases, DR_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr_check dr SPI0_RX0 (THE dr.dr_last_read_v)` >>
Q.EXISTS_TAC `spi` >> rw [] >-
(`dr.dr_xfer.xfer_cur_length < (LENGTH dr.dr_xfer.xfer_dataOUT_buf)` by fs [ref_rel_def] >>
rw [dr_check_def, dr_check_rx0_def] >>
fs [ref_rel_def, IS_STATE_REL_def]) >>
`~ (dr.dr_xfer.xfer_cur_length < (LENGTH dr.dr_xfer.xfer_dataOUT_buf))` by fs [ref_rel_def] >>
rw [dr_check_def, dr_check_rx0_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* simulation: (dr',spi') exists and holds the ref_rel when ds_abs1 has tau_dr transitions *)
val abs1_comb_hold_ref_rel_tau_dr = 
store_thm("abs1_comb_hold_ref_rel_tau_dr",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_dr_tr ds_abs1 tau_dr ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))``,
rw [ds_abs1_dr_tr_cases] >>
rw [abs1_comb_hold_ref_rel_tau_dr_rx, abs1_comb_hold_ref_rel_tau_dr_xfer]);

val _ = export_theory();
