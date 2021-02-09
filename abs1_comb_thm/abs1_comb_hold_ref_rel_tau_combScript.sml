open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory weak_bisimulationTheory SPI_tauTheory SPI_update_regsTheory SPI_return_regsTheory;
open driver_stateTheory driver_relationTheory driver_writeTheory driver_readTheory driver_checkTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory board_memTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_tau_comb";

(* a basic theorem for word1*)
val word1_not_1w_eq_0w = store_thm("word1_not_1w_eq_0w",
``!w:word1. w <> 1w:word1 ==> w = 0w:word1``,
Cases_on `w` >> rw [] >>
FULL_SIMP_TAC (arith_ss++WORD_ss) []);

(* theorems related to init automaton *)
(* (dr',spi') exists for init *)
val abs1_comb_hold_ref_rel_tau_comb_init = store_thm("abs1_comb_hold_ref_rel_tau_comb_init",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_init_start) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (ds_abs1 with state := abs1_ready) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (ds_abs1 with state := abs1_ready) (dr',spi')))``,
cheat);

(* theorems related to tx automaton *)
(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_trans *)
val ref_rel_holds_tau_comb_abs1_tx_trans = store_thm("ref_rel_holds_tau_comb_abs1_tx_trans",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_trans) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length = dr.dr_tx.tx_cur_length` by fs [ref_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.tx_data_buf` by fs [ref_rel_def] >>
`(dr.state = dr_tx_write_data /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_read_txs /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_ready_for_trans)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_tx_write_data and tx_ready_for_trans *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def,
SPI0_CH0CTRL_def, write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_read_txs and tx_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_check_txs and tx_ready_for_trans *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_txs` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_tx_read_txs) = dr with <| state := dr_tx_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_done_2 *)
val ref_rel_holds_tau_comb_abs1_tx_done_2 = store_thm("ref_rel_holds_tau_comb_abs1_tx_done_2",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_done_2) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length = dr.dr_tx.tx_cur_length` by fs [ref_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.tx_data_buf` by fs [ref_rel_def] >>
`(dr.state = dr_tx_write_data /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_read_txs /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_done)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_tx_write_data and tx_trans_done *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def,
SPI0_CH0CTRL_def, write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_read_txs and tx_trans_done *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_check_txs and tx_trans_done *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_txs` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_tx_read_txs) = dr with <| state := dr_tx_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_reset *)
val ref_rel_holds_tau_comb_abs1_tx_reset = store_thm("ref_rel_holds_tau_comb_abs1_tx_reset",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_reset) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def] >>
`(dr.state = dr_tx_reset_conf /\ spi.state = tx_channel_disabled) \/
(dr.state = dr_tx_issue_disable /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_read_eot /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_ready_for_trans)` by fs [IS_STATE_REL_def] >|
[(* dr_tx_reset_conf and tx_channel_disabled *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_tx_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def,
write_CH0CONF_comb_def, write_CH0CONF_tx_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_issue_disable and tx_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0:num` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_write_state dr = dr with state := dr_tx_reset_conf` 
by rw [dr_write_state_def, dr_write_def, dr_write_ch0ctrl_def] >>
rw [] >>
Q.EXISTS_TAC `dr_write_state (dr with state := dr_tx_reset_conf)` >>
Q.EXISTS_TAC `write_SPI_regs (THE (dr_write_address (dr with state := dr_tx_reset_conf)))
(THE (dr_write_value (dr with state := dr_tx_reset_conf)))
(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)` >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_tx_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_tx_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_read_eot and tx_ready_for_trans *)
DISJ2_TAC >>
`spi.regs.CH0STAT.EOT = 1w /\ spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >>
Q.EXISTS_TAC `SUC 2:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_eot; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
`dr_check (dr with <| state := dr_tx_check_eot; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |>) 
SPI0_CH0STAT (build_CH0STAT spi.regs.CH0STAT) = 
dr with <| state := dr_tx_issue_disable; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |> ` 
by (rw [dr_check_def, dr_check_tx_ch0stat_def,build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []) >>
rw [] >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_tx_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_tx_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_check_eot and tx_ready_for_trans *)
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
DISJ2_TAC >>
Cases_on `(2 >< 2) v:word1 = 1w /\ (1 >< 1) v:word1 = 1w` >|
[(* the stored values of txs and eot are 1w *)
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_issue_disable` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [] >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_tx_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_tx_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* the stored values are not 1w *)
Q.EXISTS_TAC `SUC 3` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_eot` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [] >>
`spi.regs.CH0STAT.EOT = 1w /\ spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >>
`dr_read (dr with state := dr_tx_read_eot) = 
dr with <| state := dr_tx_check_eot; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
`dr_check (dr with <| state := dr_tx_check_eot; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |>) 
SPI0_CH0STAT (build_CH0STAT spi.regs.CH0STAT) = 
dr with <| state := dr_tx_issue_disable; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |> ` 
by (rw [dr_check_def, dr_check_tx_ch0stat_def,build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []) >>
rw [] >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_tx_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_tx_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]]);

(* (dr', spi') exists for tx *)
val abs1_comb_hold_ref_rel_tau_comb_tx = store_thm("abs1_comb_hold_ref_rel_tau_comb_tx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_TX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_TX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_tx_trans, ref_rel_holds_tau_comb_abs1_tx_done_2,
ref_rel_holds_tau_comb_abs1_tx_reset]);


(* theorems related to rx automaton *)
(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_rx_read *)
val ref_rel_holds_tau_comb_abs1_rx_read = store_thm("ref_rel_holds_tau_comb_abs1_rx_read",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_rx_read) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr', spi'))``,
rw [comb_abs1_rx_operations_def, comb_abs1_rx_read_op_def] >>
`dr.state = dr_rx_read_rx0 /\ spi.state = rx_data_ready` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >>
rw [dr_read_def, dr_read_rx0_def, read_SPI_regs_value_def, read_SPI_regs_state_def,
read_SPI_regs_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def,
SPI0_CH0CTRL_def, SPI0_CH0STAT_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) []);

(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_rx_reset *)
val ref_rel_holds_tau_comb_abs1_rx_reset = store_thm("ref_rel_holds_tau_comb_abs1_rx_reset",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_rx_reset) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_rx_operations_def, comb_abs1_rx_reset_op_def] >>
`(dr.state = dr_rx_reset_conf /\ spi.state = rx_channel_disabled) \/
(dr.state = dr_rx_issue_disable /\ spi.state = rx_data_ready)` by fs [IS_STATE_REL_def] >-
((* dr_rx_reset_conf and rx_rx_channel_disabled *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_rx_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def,
write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
fs [ref_rel_def, IS_STATE_REL_def]) >>
(* dr_rx_issue_disable and rx_data_ready *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0:num` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_write_state dr = dr with state := dr_rx_reset_conf` 
by rw [dr_write_state_def, dr_write_def, dr_write_ch0ctrl_def] >>
rw [] >>
Q.EXISTS_TAC `dr_write_state (dr with state := dr_rx_reset_conf)` >>
Q.EXISTS_TAC `write_SPI_regs (THE (dr_write_address (dr with state := dr_rx_reset_conf)))
(THE (dr_write_value (dr with state := dr_rx_reset_conf)))
(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)` >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_rx_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_rx_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (ds',spi') exists for rx *)
val abs1_comb_hold_ref_rel_tau_comb_rx = store_thm("abs1_comb_hold_ref_rel_tau_comb_rx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_RX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_RX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_rx_read, ref_rel_holds_tau_comb_abs1_rx_reset]);


(* theorems related to xfer automaton *)
(* ref_rel holds when ds_abs1 has tau_comb transition and ds_abs1.state = abs1_xfer_prepare *)
val ref_rel_holds_tau_comb_abs1_xfer_prepare = store_thm("ref_rel_holds_tau_comb_abs1_xfer_prepare",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_prepare) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def] >>
`(dr.state = dr_xfer_write_dataO /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_read_txs /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_check_txs /\ spi.state = xfer_ready_for_trans)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_xfer_write_dataO and xfer_ready_for_trans *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def,
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* dr_xfer_read_txs and xfer_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_xfer_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [],
(* dr_xfer_check_txs and xfer_ready_for_trans *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def,
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_xfer_read_txs` 
by rw [dr_check_def, dr_check_xfer_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_xfer_read_txs) = dr with <| state := dr_xfer_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);


(* ref_rel holds when ds_abs1 has tau_comb transition and ds_abs1.state = abs1_xfer_ready *)
val ref_rel_holds_tau_comb_abs1_xfer_ready = store_thm("ref_rel_holds_tau_comb_abs1_xfer_ready",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_ready) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_ready_op_def] >>
`(dr.state = dr_xfer_read_rx0 /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_read_rxs /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_data_ready)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >|
[(* dr_xfer_read_rx0 and xfer_data_ready *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_xfer_read_rxs and xfer_data_ready *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_xfer_check_rxs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [],
(* dr_xfer_check_rxs and xfer_data_ready *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(0 >< 0) v:word1 = 1w` >|
[(* the stored value of rxs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* the stored value of rxs is 0w *)
`(0 >< 0) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_xfer_read_rxs` 
by rw [dr_check_def, dr_check_xfer_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_xfer_read_rxs) = dr with <| state := dr_xfer_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* ref_rel holds when ds_abs1 has tau_comb transition and ds_abs1.state = abs1_xfer_reset *)
val ref_rel_holds_tau_comb_abs1_xfer_reset = store_thm("ref_rel_holds_tau_comb_abs1_xfer_reset",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_reset) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_reset_op_def] >>
`(dr.state = dr_xfer_reset_conf /\ spi.state = xfer_channel_disabled) \/
(dr.state = dr_xfer_issue_disable /\ spi.state = xfer_ready_for_trans)` by fs [IS_STATE_REL_def] >-
((* dr_xfer_reset_conf and xfer_channel_disabled *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def, 
dr_write_ch0conf_xfer_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_CH0CONF_comb_def,
write_CH0CONF_xfer_def] >>
fs [ref_rel_def, IS_STATE_REL_def]) >>
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0:num` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_write_state dr = dr with state := dr_xfer_reset_conf` 
by rw [dr_write_state_def, dr_write_def, dr_write_ch0ctrl_def] >>
rw [] >>
Q.EXISTS_TAC `dr_write_state (dr with state := dr_xfer_reset_conf)` >>
Q.EXISTS_TAC `write_SPI_regs (THE (dr_write_address (dr with state := dr_xfer_reset_conf)))
(THE (dr_write_value (dr with state := dr_xfer_reset_conf)))
(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)` >>
rw [dr_write_address_def, dr_write_state_def, dr_write_value_def, dr_write_def,
dr_write_ch0conf_xfer_def, dr_write_ch0ctrl_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CONF_comb_def, 
write_CH0CTRL_def, write_CH0CONF_xfer_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for xfer *)
val abs1_comb_hold_ref_rel_tau_comb_xfer = store_thm("abs1_comb_hold_ref_rel_tau_comb_xfer",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_XFER_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_XFER_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_xfer_prepare, ref_rel_holds_tau_comb_abs1_xfer_ready, 
ref_rel_holds_tau_comb_abs1_xfer_reset]);

(* simulation: (dr',spi') exists and holds the ref_rel when ds_abs1 has tau_comb transitions *)
val abs1_comb_hold_ref_rel_tau_comb = store_thm("abs1_comb_hold_ref_rel_tau_comb",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))``,
rw [ds_abs1_comb_tr_cases, COMB_ABS1_INIT_ENABLE_def, 
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
rw [abs1_comb_hold_ref_rel_tau_comb_init, abs1_comb_hold_ref_rel_tau_comb_tx,
abs1_comb_hold_ref_rel_tau_comb_rx, abs1_comb_hold_ref_rel_tau_comb_xfer]);

val _ = export_theory();
