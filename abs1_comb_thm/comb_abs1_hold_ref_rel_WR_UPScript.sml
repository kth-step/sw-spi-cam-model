open HolKernel bossLib boolLib Parse;
open wordsLib pred_setLib;
open SPI_stateTheory SPI_relationTheory SPI_update_regsTheory;
open driver_stateTheory driver_relationTheory driver_writeTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory 
ds_abs1_rxTheory ds_abs1_xferTheory;
open ref_relTheory board_memTheory;

val _ = new_theory "comb_abs1_hold_ref_rel_WR_UP";


(* relation holds when driver state is dr_init_idle *)
val ref_rel_hold_dr_init_idle_WR = store_thm("ref_rel_hold_dr_init_idle_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_idle) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_softreset_def, write_SPI_regs_def] >|
[FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def],
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_SYSCONFIG_comb_def, write_SOFTRESET_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []]);


(* relation holds for ds_abs1 or ds_abs1' when driver state is dr_init_setting *)
val ref_rel_hold_dr_init_setting_WR = store_thm("ref_rel_hold_dr_init_setting_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_setting) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
(ref_rel ds_abs1 ((dr_write_state dr), spi')) \/
(?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\ 
(ref_rel ds_abs1' ((dr_write_state dr), spi')))``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,dr_write_def] >|
[ (* update SYSCONFIG *)
rw [dr_write_sysconfig_def, write_SPI_regs_def, SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def] >|
[DISJ2_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def, 
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [ref_rel_def],
DISJ1_TAC >>
rw [write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >|
[METIS_TAC [ref_rel_def],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [],
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw []]],
(* update MODULCTRL *)
rw [dr_write_modulctrl_def, write_SPI_regs_def, SPI0_MODULCTRL_def, SPI0_SYSCONFIG_def, 
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >|
[DISJ2_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def, write_MODULCTRL_def, comb_abs1_init_operations_def, 
comb_abs1_init_start_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [ref_rel_def],
DISJ1_TAC >>
rw [write_MODULCTRL_def] >|
[METIS_TAC [ref_rel_def],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [],
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw []]],
(* update CH0CONF.WL *)
rw [dr_write_ch0conf_wl_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def, 
SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >|
[DISJ2_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def, write_CH0CONF_comb_def, write_CH0CONF_WL_def,
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >|
[FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [],
METIS_TAC [ref_rel_def],
UNDISCH_TAC ``~(7w:word5 >+ 2w:word5)`` >>
EVAL_TAC],
DISJ1_TAC >>
rw [write_CH0CONF_comb_def, write_CH0CONF_WL_def] >|
[METIS_TAC [ref_rel_def],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [],
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
UNDISCH_TAC ``~(7w:word5 >+ 2w:word5)`` >>
EVAL_TAC]],
(* update CH0CONF.IS,DPE,TRM etc bits *)
rw [dr_write_ch0conf_mode_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def, 
SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >|
[DISJ2_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def, write_CH0CONF_comb_def, write_CH0CONF_def,
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [ref_rel_def],
DISJ1_TAC >>
rw [write_CH0CONF_comb_def, write_CH0CONF_def] >|
[METIS_TAC [ref_rel_def],
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [],
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw []]],
(* update CH0CONF.CLKD *)
rw [dr_write_ch0conf_speed_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def, 
SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def] >>
DISJ2_TAC >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
EXISTS_TAC ``comb_abs1_init_operations ds_abs1`` >>
rw [COMB_ABS1_INIT_ENABLE_def, write_CH0CONF_comb_def, write_CH0CONF_speed_def,
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw [] >>
METIS_TAC [ref_rel_def]]);


(* relation holds when driver state is dr_tx_idle *)
val ref_rel_hold_dr_tx_idle_WR = store_thm("ref_rel_hold_dr_tx_idle_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_idle) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_tx_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_tx_conf_issued *)
val ref_rel_hold_dr_tx_conf_issued_WR = store_thm("ref_rel_hold_dr_tx_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* ds_abs1' exists and ref_rel holds when driver state is dr_tx_write_data *)
val ref_rel_hold_dr_tx_write_data_WR = store_thm("ref_rel_hold_dr_tx_write_data_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_write_data) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >|
[(* abs1_tx_trans *)
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_trans_op_def] >|
[`dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
rw [] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
`~ (dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1)` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
rw [] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []],
(* abs1_tx_done_2 *)
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_done_2_op_def] >|
[`dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
rw [] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
`~ (dr.dr_tx.tx_cur_length < (LENGTH dr.dr_tx.tx_data_buf) - 1)` by METIS_TAC[ref_rel_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def, 
dr_write_tx0_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
rw [] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* relation holds when driver state is dr_tx_issue_disable *)
val ref_rel_hold_dr_tx_issue_disable_WR = store_thm("ref_rel_hold_dr_tx_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* ds_abs1' exists and ref_rel holds when driver state is dr_tx_reset_conf *)
val ref_rel_hold_dr_tx_reset_conf_WR = store_thm("ref_rel_hold_dr_tx_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
EXISTS_TAC ``comb_abs1_tx_operations ds_abs1`` >>
rw [COMB_ABS1_TX_ENABLE_def] >>
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def, dr_write_state_def, 
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_tx_def, 
write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_tx_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_rx_idle *)
val ref_rel_hold_dr_rx_idle_WR = store_thm("ref_rel_hold_dr_rx_idle_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_idle) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_rx_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_rx_conf_issued *)
val ref_rel_hold_dr_rx_conf_issued_WR = store_thm("ref_rel_hold_dr_rx_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_rx_issue_disable *)
val ref_rel_hold_dr_rx_issue_disable_WR = store_thm("ref_rel_hold_dr_rx_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []); 

(* ds_abs1' exists and ref_rel holds when driver state is dr_rx_reset_conf *)
val ref_rel_hold_dr_rx_reset_conf_WR = store_thm("ref_rel_hold_dr_rx_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
EXISTS_TAC ``comb_abs1_rx_operations ds_abs1`` >>
rw [COMB_ABS1_RX_ENABLE_def] >>
rw [comb_abs1_rx_operations_def, comb_abs1_rx_reset_op_def, dr_write_state_def, 
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_rx_def, 
write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_rx_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_xfer_idle *)
val ref_rel_hold_dr_xfer_idle_WR = store_thm("ref_rel_hold_dr_xfer_idle_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_idle) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_xfer_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_xfer_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* relation holds when driver state is dr_xfer_conf_issued *)
val ref_rel_hold_dr_xfer_conf_issued_WR = store_thm("ref_rel_hold_dr_xfer_conf_issued_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_conf_issued) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* ds_abs1' exists and ref_rel holds when driver state is dr_xfer_write_dataO *)
val ref_rel_hold_dr_xfer_write_dataO_WR = store_thm("ref_rel_hold_dr_xfer_write_dataO_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_write_dataO) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [COMB_ABS1_XFER_ENABLE_def] >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def,
dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_CH0CONF_def,SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, SPI0_TX0_def] >>
rw [write_TX0_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def, CHECK_TXS_BIT_def] >>
rw [] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* relation holds when driver state is dr_xfer_issue_disable *)
val ref_rel_hold_dr_xfer_issue_disable_WR = store_thm("ref_rel_hold_dr_xfer_issue_disable_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_issue_disable) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
ref_rel ds_abs1 ((dr_write_state dr), spi')``,
rw [spi_tr_cases] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0ctrl_def, write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,
SPI0_MODULCTRL_def, SPI0_CH0CTRL_def] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
rw [write_CH0CTRL_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

(* ds_abs1' exists and ref_rel holds when driver state is dr_xfer_reset_conf *)
val ref_rel_hold_dr_xfer_reset_conf_WR = store_thm("ref_rel_hold_dr_xfer_reset_conf_WR",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_reset_conf) /\
(spi_tr spi (Update (THE (dr_write_address dr)) (THE (dr_write_value dr))) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_write_state dr), spi'))``,
rw [spi_tr_cases, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`IS_STATE_REL ds_abs1 dr spi` by METIS_TAC [ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_STATE_REL_def] >>
rw [] >>
Cases_on `dr.state` >>
rw [] >>
Cases_on `ds_abs1.state` >>
rw [] >>
Cases_on `spi.state` >>
rw [] >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [COMB_ABS1_XFER_ENABLE_def] >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_reset_op_def, dr_write_state_def, 
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_xfer_def, 
write_SPI_regs_def] >>
FULL_SIMP_TAC (std_ss++PRED_SET_ss++WORD_ss) 
[SPI0_SYSCONFIG_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_CH0CONF_def,SPI0_MODULCTRL_def] >>
rw [write_CH0CONF_comb_def, write_CH0CONF_xfer_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def, IS_STATE_REL_def] >>
rw []);

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
METIS_TAC [ref_rel_hold_dr_tx_idle_WR],
METIS_TAC [ref_rel_hold_dr_tx_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_tx_write_data_WR],
METIS_TAC [ref_rel_hold_dr_tx_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_tx_reset_conf_WR],
METIS_TAC [ref_rel_hold_dr_rx_idle_WR],
METIS_TAC [ref_rel_hold_dr_rx_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_rx_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_rx_reset_conf_WR],
METIS_TAC [ref_rel_hold_dr_xfer_idle_WR],
METIS_TAC [ref_rel_hold_dr_xfer_conf_issued_WR],
METIS_TAC [ref_rel_hold_dr_xfer_write_dataO_WR],
METIS_TAC [ref_rel_hold_dr_xfer_issue_disable_WR],
METIS_TAC [ref_rel_hold_dr_xfer_reset_conf_WR]]);

val _ = export_theory();
