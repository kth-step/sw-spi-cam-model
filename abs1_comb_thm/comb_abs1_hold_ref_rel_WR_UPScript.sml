open HolKernel bossLib boolLib Parse wordsLib pred_setLib;
open SPI_stateTheory SPI_relationTheory SPI_update_regsTheory SPI_return_regsTheory driver_stateTheory driver_relationTheory driver_writeTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "comb_abs1_hold_ref_rel_WR_UP";

(* relation holds when driver state is dr_init_idle *)
val ref_rel_hold_dr_init_idle_WR = store_thm("ref_rel_hold_dr_init_idle_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_idle) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_softreset_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_SYSCONFIG_comb_def, write_SOFTRESET_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
METIS_TAC []);


(* relation holds for ds_abs1 or ds_abs1' when driver state is dr_init_setting *)
val ref_rel_hold_dr_init_setting_WR = store_thm("ref_rel_hold_dr_init_setting_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_setting) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
(ref_rel ds_abs1 ((dr_write_state dr), spi')) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' ((dr_write_state dr), spi')))``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,dr_write_def] >| [
(* update SYSCONFIG *)
rw [dr_write_sysconfig_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def,SPI0_START_def, SPI0_END_def] >>
DISJ1_TAC >>
rw [write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >|
[METIS_TAC [ref_rel_def],
fs [ref_rel_def, IS_STATE_REL_def] >>
METIS_TAC [],
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw []],
(* update MODULCTRL *)
rw [dr_write_modulctrl_def, write_SPI_regs_def, SPI0_MODULCTRL_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >>
DISJ1_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [write_MODULCTRL_def] >-
(`spi.regs.CH0CONF.WL = 0w` by fs [ref_rel_def] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
fs []) >>
fs [ref_rel_def, IS_STATE_REL_def] >>
METIS_TAC [],
(* update CH0CONF *)
rw [dr_write_ch0conf_init_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def, 
SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
`spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) spi` by fs [ch0conf_changed_def] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_init_def] >-
(DISJ2_TAC >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def,comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
fs [ref_rel_def, IS_STATE_REL_def]) >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
METIS_TAC [ref_rel_def]]);

(* relation holds when driver state is dr_tx_fetch_conf *)
val ref_rel_hold_dr_tx_fetch_conf_WR = store_thm("ref_rel_hold_dr_tx_fetch_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_fetch_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1056768w:word32)) : word2 = 2w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_tx_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_tx_conf_issued *)
val ref_rel_hold_dr_tx_conf_issued_WR = store_thm("ref_rel_hold_dr_tx_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, 
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ds_abs1' exists and ref_rel holds when driver state is dr_tx_write_data *)
val ref_rel_hold_dr_tx_write_data_WR = store_thm("ref_rel_hold_dr_tx_write_data_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_write_data) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >|
[(* abs1_tx_trans *)
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def] >|
[`dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1` by METIS_TAC [ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def, 
SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
fs [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
`~ (dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1)` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def, 
SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >> 
fs [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []],
(* abs1_tx_done_2 *)
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_done_2_op_def] >|
[`dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def, 
SPI0_CH0CTRL_def, SPI0_TX0_def, write_TX0_def] >>
fs [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
`~ (dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1)` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def, 
SPI0_CH0CTRL_def, SPI0_TX0_def, write_TX0_def] >>
fs [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* relation holds when driver state is dr_tx_issue_disable *)
val ref_rel_hold_dr_tx_issue_disable_WR = store_thm("ref_rel_hold_dr_tx_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, 
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ds_abs1' exists and ref_rel holds when driver state is dr_tx_reset_conf *)
val ref_rel_hold_dr_tx_reset_conf_WR = store_thm("ref_rel_hold_dr_tx_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, dr_write_state_def, 
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_tx_def, 
write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >> 
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_CH0CONF_comb_def,write_CH0CONF_tx_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_rx_fetch_conf *)
val ref_rel_hold_dr_rx_fetch_conf_WR = store_thm("ref_rel_hold_dr_rx_fetch_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_fetch_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_rx_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >> rw [] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1052672w:word32)) :word2 = 1w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_rx_conf_issued *)
val ref_rel_hold_dr_rx_conf_issued_WR = store_thm("ref_rel_hold_dr_rx_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_rx_issue_disable *)
val ref_rel_hold_dr_rx_issue_disable_WR = store_thm("ref_rel_hold_dr_rx_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]); 

(* ds_abs1' exists and ref_rel holds when driver state is dr_rx_reset_conf *)
val ref_rel_hold_dr_rx_reset_conf_WR = store_thm("ref_rel_hold_dr_rx_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [dr_write_state_def, dr_write_value_def,dr_write_address_def, dr_write_def,
dr_write_ch0conf_rx_def, write_SPI_regs_def, SPI0_SYSCONFIG_def,SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_xfer_idle *)
val ref_rel_hold_dr_xfer_fetch_conf_WR = store_thm("ref_rel_hold_dr_xfer_fetch_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_fetch_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_xfer_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) spi)` by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) : word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293906431w:word32) && (build_CH0CONF spi.regs.CH0CONF) || 
(1048576w:word32)) :word2 = 0w` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_xfer_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* relation holds when driver state is dr_xfer_conf_issued *)
val ref_rel_hold_dr_xfer_conf_issued_WR = store_thm("ref_rel_hold_dr_xfer_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >> rw [] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ds_abs1' exists and ref_rel holds when driver state is dr_xfer_write_dataO *)
val ref_rel_hold_dr_xfer_write_dataO_WR = store_thm("ref_rel_hold_dr_xfer_write_dataO_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_write_dataO) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [COMB_ABS1_XFER_ENABLE_def] >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def,
dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
fs [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* relation holds when driver state is dr_xfer_issue_disable *)
val ref_rel_hold_dr_xfer_issue_disable_WR = store_thm("ref_rel_hold_dr_xfer_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [write_CH0CTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* ds_abs1' exists and ref_rel holds when driver state is dr_xfer_reset_conf *)
val ref_rel_hold_dr_xfer_reset_conf_WR = store_thm("ref_rel_hold_dr_xfer_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `dr.state` >> rw [] >>
Cases_on `ds_abs1.state` >> rw [] >>
Cases_on `spi.state` >> rw [] >>
rw [dr_write_state_def,dr_write_value_def,dr_write_address_def, dr_write_def,
dr_write_ch0conf_xfer_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_CH0CONF_comb_def, write_CH0CONF_xfer_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* simulation: ref_rel holds for ds_abs1 or ds_abs1' when driver and controller perform WRITE and UPDATE operations *)
val comb_abs1_hold_ref_rel_WR_UP = store_thm("comb_abs1_hold_ref_rel_WR_UP",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (a:word32) (v:word32) 
(spi':spi_state) (dr':driver_state).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (Write a v) dr') /\ 
(spi_tr spi (Update a v) spi') ==>
(ref_rel ds_abs1 (dr', spi')) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' (dr', spi')))``,
rw [driver_tr_cases, DR_WR_ENABLE_def] >|
[METIS_TAC [ref_rel_hold_dr_init_idle_WR],
METIS_TAC [ref_rel_hold_dr_init_setting_WR],
METIS_TAC [ref_rel_hold_dr_tx_fetch_conf_WR],
METIS_TAC [ref_rel_hold_dr_tx_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_tx_write_data_WR],
METIS_TAC [ref_rel_hold_dr_tx_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_tx_reset_conf_WR],
METIS_TAC [ref_rel_hold_dr_rx_fetch_conf_WR],
METIS_TAC [ref_rel_hold_dr_rx_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_rx_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_rx_reset_conf_WR],
METIS_TAC [ref_rel_hold_dr_xfer_fetch_conf_WR],
METIS_TAC [ref_rel_hold_dr_xfer_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_xfer_write_dataO_WR],
METIS_TAC [ref_rel_hold_dr_xfer_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_xfer_reset_conf_WR]]);

val _ = export_theory();
