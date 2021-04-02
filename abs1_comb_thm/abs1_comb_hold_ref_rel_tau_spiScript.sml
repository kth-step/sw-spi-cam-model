open HolKernel bossLib boolLib Parse wordsLib;
open SPI_stateTheory SPI_relationTheory weak_bisimulationTheory SPI_tauTheory SPI_update_regsTheory SPI_return_regsTheory driver_stateTheory driver_relationTheory driver_writeTheory driver_readTheory driver_checkTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_tau_spi";

(* related to tx automaton *)
(* ref_rel holds if ds_abs1 has tau_spi transition and ds_abs1.state = abs1_tx_idle *)
val ref_rel_holds_tau_spi_abs1_tx_idle = store_thm("ref_rel_holds_tau_spi_abs1_tx_idle",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_tx_idle) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [spi_abs1_tx_operations_def, spi_abs1_tx_idle_op_def] >>
`(dr.state = dr_tx_read_txs /\ spi.state = tx_channel_enabled) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_channel_enabled) \/
(dr.state = dr_tx_conf_issued /\ spi.state = tx_conf_ready) \/
(dr.state = dr_tx_fetch_conf /\ spi.state = spi_ready) \/
(dr.state = dr_tx_idle /\ spi.state = spi_ready)` 
by fs [IS_STATE_REL_def] >|
[(* dr_tx_read_txs and tx_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_check_txs and tx_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_conf_issued and tx_conf_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``dr_write_state dr: driver_state`` >>
EXISTS_TAC ``spi_tau_operations (write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)`` >>
EXISTS_TAC ``(dr_write_state dr, 
write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)`` >>
rw [] >|
[DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, SPI_TAU_ENABLE_def, dr_write_ch0ctrl_def, write_CH0CTRL_def] >>
fs [SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def],
fs [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_state_def, dr_write_def, dr_write_ch0ctrl_def, write_CH0CTRL_def] >>
rw [SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_tx_fetch_conf and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_def, dr_write_ch0conf_tx_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`(THE (dr_write_address dr) = SPI0_CH0CONF) /\ 
(THE (dr_write_value dr) = (4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32))` by fs [dr_write_address_def, dr_write_value_def, 
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word2 = 2w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi) = 
spi with <| state := tx_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 2w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_tx_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with state := dr_tx_read_txs` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs (THE (dr_write_address (dr with state := dr_tx_conf_issued)))
(THE (dr_write_value (dr with state := dr_tx_conf_issued)))
(spi with <| state := tx_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 2w; FORCE := 1w |> |>))` >>
rw [] >|
[DISJ1_TAC >> 
DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def, write_CH0CTRL_def],
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_tx_idle and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <|state := dr_tx_fetch_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF spi = spi)`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word2 = 2w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs SPI0_CH0CONF 
((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || (1056768w:word32):word32) spi) = 
spi with <| state := tx_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 2w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_tx_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with <|state := dr_tx_read_txs;
dr_last_read_ad := SOME SPI0_CH0CONF; 
dr_last_read_v := SOME (build_CH0CONF spi.regs.CH0CONF)|>` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs SPI0_CH0CTRL 1w
(spi with <| state := tx_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 2w; FORCE := 1w |> |>))` >>
rw [] >|
[DISJ1_TAC >> 
DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def,SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, 
SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def,
write_CH0CTRL_def],
rw [write_SPI_regs_def,SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, 
SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, tx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]]);

(* ref_rel holds if ds_abs1 has tau_spi transition and ds_abs1.state = abs1_tx_data_1 *)
val ref_rel_holds_tau_spi_abs1_tx_data_1 = store_thm("ref_rel_holds_tau_spi_abs1_tx_data_1",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_tx_data_1) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_1_op_def] >>
`(dr.state = dr_tx_read_eot /\ spi.state = tx_trans_data) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_trans_data)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 has tau_spi transition and ds_abs1.state = abs1_tx_data_2 *)
val ref_rel_holds_tau_spi_abs1_tx_data_2 = store_thm("ref_rel_holds_tau_spi_abs1_tx_data_2",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_tx_data_2) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_tx_operations_def, spi_abs1_tx_data_2_op_def] >>
`(dr.state = dr_tx_read_txs /\ spi.state = tx_trans_data) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_data)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 has tau_spi transition and ds_abs1.state = abs1_tx_update *)
val ref_rel_holds_tau_spi_abs1_tx_update = store_thm("ref_rel_holds_tau_spi_abs1_tx_update",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_tx_update) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_tx_operations_def, spi_abs1_tx_update_op_def] >>
`(dr.state = dr_tx_read_txs /\ spi.state = tx_trans_update) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_update)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_trans_update_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 has tau_spi transition and ds_abs1.state = abs1_tx_update *)
val ref_rel_holds_tau_spi_abs1_tx_last_update = store_thm("ref_rel_holds_tau_spi_abs1_tx_last_update",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_tx_last_update) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_tx_operations_def, spi_abs1_tx_last_update_op_def] >>
`(dr.state = dr_tx_read_eot /\ spi.state = tx_trans_update) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_trans_update)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, tx_trans_update_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for tx automaton *)
val abs1_comb_hold_ref_rel_tau_spi_tx = store_thm("abs1_comb_hold_ref_rel_tau_spi_tx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (SPI_ABS1_TX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (spi_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [SPI_ABS1_TX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_spi_abs1_tx_idle, ref_rel_holds_tau_spi_abs1_tx_data_1,
ref_rel_holds_tau_spi_abs1_tx_data_2, ref_rel_holds_tau_spi_abs1_tx_update,
ref_rel_holds_tau_spi_abs1_tx_last_update]);


(* related to rx automaton *)
(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_rx_idle *)
val ref_rel_holds_tau_spi_abs1_rx_idle = store_thm("ref_rel_holds_tau_spi_abs1_rx_idle",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_idle) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr',spi')))``,
rw [spi_abs1_rx_operations_def, spi_abs1_rx_idle_op_def] >>
`(dr.state = dr_rx_read_rxs /\ spi.state = rx_channel_enabled) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_channel_enabled) \/
(dr.state = dr_rx_conf_issued /\ spi.state = rx_conf_ready) \/
(dr.state = dr_rx_fetch_conf /\ spi.state = spi_ready) \/
(dr.state = dr_rx_idle /\ spi.state = spi_ready)` by fs [IS_STATE_REL_def] >|
[(* dr_rx_read_rxs and rx_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_rx_check_rxs and rx_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_rx_conf_issued and rx_conf_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
EXISTS_TAC ``dr_write_state dr: driver_state`` >>
EXISTS_TAC ``spi_tau_operations (write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi)`` >>
rw [] >|
[DISJ2_TAC >> 
DISJ1_TAC >>
NTAC 4 DISJ2_TAC >>
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_ch0ctrl_def, write_CH0CTRL_def , SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, 
SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def],
fs [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_state_def, 
dr_write_def, dr_write_ch0ctrl_def, write_CH0CTRL_def] >>
rw [SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_rx_fetch_conf and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_def, dr_write_ch0conf_rx_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`(THE (dr_write_address dr) = SPI0_CH0CONF) /\ 
(THE (dr_write_value dr) = (4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32))` by fs [dr_write_address_def, dr_write_value_def, 
dr_write_def, dr_write_ch0conf_rx_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) : word2 = 1w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi) = 
spi with <| state := rx_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 1w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_rx_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with state := dr_rx_read_rxs` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs (THE (dr_write_address (dr with state := dr_rx_conf_issued)))
(THE (dr_write_value (dr with state := dr_rx_conf_issued)))
(spi with <| state := rx_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 1w; FORCE := 1w |> |>))` >> rw [] >|
[DISJ1_TAC >> 
NTAC 4 DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def, write_CH0CTRL_def],
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_rx_idle and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <|state := dr_rx_fetch_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF spi = spi)`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_rx_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) : word2 = 1w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs SPI0_CH0CONF 
((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || (1052672w:word32):word32) spi) = 
spi with <| state := rx_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 1w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_rx_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with <|state := dr_rx_read_rxs;
dr_last_read_ad := SOME SPI0_CH0CONF;
dr_last_read_v := SOME (build_CH0CONF spi.regs.CH0CONF)|>` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs SPI0_CH0CTRL 1w
(spi with <| state := rx_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 1w; FORCE := 1w |> |>))` >> rw [] >|
[DISJ1_TAC >> 
NTAC 4 DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def, write_CH0CTRL_def],
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, rx_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]]);

(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_rx_update *)
val ref_rel_holds_tau_spi_abs1_rx_update = store_thm("ref_rel_holds_tau_spi_abs1_rx_update",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_update) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_rx_operations_def, spi_abs1_rx_update_op_def] >>
`(dr.state = dr_rx_read_rxs /\ spi.state = rx_update_RX0) \/
(dr.state = dr_rx_check_rxs /\ spi.state = rx_update_RX0)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, rx_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) []);

(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_rx_next *)
val ref_rel_holds_tau_spi_abs1_rx_next = store_thm("ref_rel_holds_tau_spi_abs1_rx_next",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_rx_next) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_rx_operations_def, spi_abs1_rx_next_op_def] >>
`dr.state = dr_rx_fetch_data /\ spi.state = rx_update_RX0` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, rx_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) []);

(* (dr',spi') exists for rx automaton *)
val abs1_comb_hold_ref_rel_tau_spi_rx = store_thm("abs1_comb_hold_ref_rel_tau_spi_rx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (SPI_ABS1_RX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (spi_abs1_rx_operations ds_abs1) (dr',spi')))``,
rw [SPI_ABS1_RX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_spi_abs1_rx_idle, ref_rel_holds_tau_spi_abs1_rx_update,
ref_rel_holds_tau_spi_abs1_rx_next]);


(* related to xfer automaton *)
(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_xfer_idle *)
val ref_rel_holds_tau_spi_abs1_xfer_idle = store_thm("ref_rel_holds_tau_spi_abs1_xfer_idle",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_xfer_idle) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. n_tau_tr n local_tr (dr,spi) tau (dr',spi') /\
ref_rel (spi_abs1_xfer_operations ds_abs1) (dr',spi'))``,
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_idle_op_def] >>
`(dr.state = dr_xfer_read_txs /\ spi.state = xfer_channel_enabled) \/
(dr.state = dr_xfer_check_txs /\ spi.state = xfer_channel_enabled) \/
(dr.state = dr_xfer_conf_issued /\ spi.state = xfer_conf_ready) \/
(dr.state = dr_xfer_fetch_conf /\ spi.state = spi_ready) \/
(dr.state = dr_xfer_idle /\ spi.state = spi_ready)` by fs [IS_STATE_REL_def] >|
[(* dr_xfer_read_txs and xfer_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr:driver_state` >>
Q.EXISTS_TAC `spi_tau_operations spi` >>
rw [spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_xfer_check_txs and xfer_channel_enabled *)
DISJ1_TAC >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
Q.EXISTS_TAC `dr:driver_state` >>
Q.EXISTS_TAC `spi_tau_operations spi` >>
rw [spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_xfer_conf_issued and xfer_conf_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
Q.EXISTS_TAC `dr_write_state dr` >>
Q.EXISTS_TAC `spi_tau_operations (write_SPI_regs (THE (dr_write_address dr)) 
(THE (dr_write_value dr)) spi)` >> rw [] >|
[DISJ2_TAC >>
DISJ1_TAC >>
NTAC 6 DISJ2_TAC >>
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_ch0ctrl_def, write_CH0CTRL_def , SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, 
SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def],
fs [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_state_def, 
dr_write_def, dr_write_ch0ctrl_def, write_CH0CTRL_def] >>
rw [SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_xfer_fetch_conf and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_def, dr_write_ch0conf_xfer_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`(THE (dr_write_address dr) = SPI0_CH0CONF) /\ 
(THE (dr_write_value dr) = (4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32))` by fs [dr_write_address_def, dr_write_value_def, 
dr_write_def, dr_write_ch0conf_xfer_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) : word2 = 0w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs (THE (dr_write_address dr)) (THE (dr_write_value dr)) spi) = 
spi with <| state := xfer_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 0w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_xfer_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with state := dr_xfer_read_txs` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs (THE (dr_write_address (dr with state := dr_xfer_conf_issued)))
(THE (dr_write_value (dr with state := dr_xfer_conf_issued)))
(spi with <| state := xfer_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 0w; FORCE := 1w |> |>))` >> rw [] >|
[DISJ1_TAC >> 
NTAC 6 DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def, write_CH0CTRL_def],
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]],
(* dr_xfer_idle and spi_ready *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_WR_ENABLE_def, GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <|state := dr_xfer_fetch_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF spi = spi)`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_xfer_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) : word2 = 0w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(write_SPI_regs SPI0_CH0CONF 
((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || (1048576w:word32):word32) spi) = 
spi with <| state := xfer_conf_ready; 
regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 0w; FORCE := 1w |> |>` by (fs [write_SPI_regs_def, write_CH0CONF_comb_def, 
write_CH0CONF_xfer_def, SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
fs [dr_write_ch0ctrl_def] >>
Q.EXISTS_TAC `dr with <|state := dr_xfer_read_txs;
dr_last_read_ad := SOME SPI0_CH0CONF; 
dr_last_read_v := SOME (build_CH0CONF spi.regs.CH0CONF)|>` >>
Q.EXISTS_TAC `spi_tau_operations 
(write_SPI_regs SPI0_CH0CTRL 1w
(spi with <| state := xfer_conf_ready; regs := spi.regs with CH0CONF := spi.regs.CH0CONF with
<|TRM := 0w; FORCE := 1w |> |>))` >>
rw [] >|
[DISJ1_TAC >> 
NTAC 6 DISJ2_TAC >> 
DISJ1_TAC >>
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def, write_CH0CTRL_def],
rw [write_SPI_regs_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def, SPI0_SYSCONFIG_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, dr_write_ch0ctrl_def] >>
rw [write_CH0CTRL_def, spi_tau_operations_def, xfer_channel_enabled_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]]]);

(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_xfer_data *)
val ref_rel_holds_tau_spi_abs1_xfer_data = store_thm("ref_rel_holds_tau_spi_abs1_xfer_data",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_xfer_data) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_xfer_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_data_op_def] >>
`(dr.state = dr_xfer_read_rxs /\ spi.state = xfer_trans_data) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_trans_data)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, xfer_trans_data_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ref_rel holds if ds_abs1 performs tau_spi transition and ds_abs1.state = abs1_xfer_update *)
val ref_rel_holds_tau_spi_abs1_xfer_update = store_thm("ref_rel_holds_tau_spi_abs1_xfer_update",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr,spi)) /\ (ds_abs1.state = abs1_xfer_update) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_xfer_operations ds_abs1) (dr', spi'))``,
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_update_op_def] >>
`(dr.state = dr_xfer_read_rxs /\ spi.state = xfer_update_RX0) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_update_RX0)` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, spi_tr_cases, SPI_TAU_ENABLE_def] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_tau_operations spi:spi_state`` >>
rw [spi_tau_operations_def, xfer_update_RX0_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* (dr',spi') exists for xfer automaton *)
val abs1_comb_hold_ref_rel_tau_spi_xfer = store_thm("abs1_comb_hold_ref_rel_tau_spi_xfer",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (SPI_ABS1_XFER_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (spi_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [SPI_ABS1_XFER_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_spi_abs1_xfer_idle, ref_rel_holds_tau_spi_abs1_xfer_data,
ref_rel_holds_tau_spi_abs1_xfer_update]);


(* simulation: (dr',spi') exists and holds the ref_rel when ds_abs1 has tau_spi *)
val abs1_comb_hold_ref_rel_tau_spi = store_thm("abs1_comb_hold_ref_rel_tau_spi",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_spi_tr ds_abs1 tau_spi ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))``,
rw [ds_abs1_spi_tr_cases] >>
rw [abs1_comb_hold_ref_rel_tau_spi_tx, abs1_comb_hold_ref_rel_tau_spi_rx,
abs1_comb_hold_ref_rel_tau_spi_xfer]);

val _ = export_theory();
