open HolKernel bossLib boolLib Parse wordsLib pred_setLib;
open SPI_stateTheory SPI_relationTheory SPI_return_regsTheory driver_stateTheory driver_relationTheory driver_readTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "comb_abs1_hold_ref_rel_RD_RE";

(* relation holds when driver state is dr_init_read_req *)
val ref_rel_hold_dr_init_read_req = store_thm("ref_rel_hold_dr_init_read_req",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_init_read_req) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_sysstatus_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_SYSSTATUS_def] >>
Cases_on `spi.state` >> rw []);

(* relation holds when driver state is dr_tx_idle *)
val ref_rel_hold_dr_tx_idle = store_thm("ref_rel_hold_dr_tx_idle",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_idle) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);

(* relation holds when driver state is dr_tx_read_txs *)
val ref_rel_hold_dr_tx_read_txs = store_thm("ref_rel_hold_dr_tx_read_txs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_read_txs) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0stat_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_CH0STAT_def, SPI0_PA_RANGE_def, SPI0_START_def,
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def,
SPI0_CH0CONF_def, build_CH0STAT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0STAT_def] >>
Cases_on `spi.state` >> rw [] >> 
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* relation holds when driver state is dr_tx_read_eot *)
val ref_rel_hold_dr_tx_read_eot = store_thm("ref_rel_hold_dr_tx_read_eot",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_read_eot) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0stat_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_CH0STAT_def, SPI0_PA_RANGE_def, SPI0_START_def,
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def,
SPI0_CH0CONF_def, build_CH0STAT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0STAT_def] >>
Cases_on `spi.state` >> rw [] >> 
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* relation holds when driver state is dr_tx_read_conf *)
val ref_rel_hold_dr_tx_read_conf = store_thm("ref_rel_hold_dr_tx_read_conf",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_tx_read_conf) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);

(* relation holds when driver state is dr_rx_idle *)
val ref_rel_hold_dr_rx_idle = store_thm("ref_rel_hold_dr_rx_idle",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_idle) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);

(* relation holds when driver state is dr_rx_read_rxs *)
val ref_rel_hold_dr_rx_read_rxs = store_thm("ref_rel_hold_dr_rx_read_rxs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_read_rxs) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0stat_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_CH0STAT_def, SPI0_PA_RANGE_def, SPI0_START_def,
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def,
SPI0_CH0CONF_def, build_CH0STAT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0STAT_def] >>
Cases_on `spi.state` >> rw [] >> 
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* lemma: if dr.state = dr_rx_read_rx0 then ds_abs1.state = abs1_rx_read
   according to ref_rel *)
val dr_rx_read_rx0_imply_abs1_rx_ready = 
store_thm("dr_rx_read_rx0_imply_abs1_rx_ready",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_read_rx0) ==>
ds_abs1.state = abs1_rx_read``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_ready) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_read_rx0) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exists and relation holds when driver state is dr_rx_read_rx0 *)
val ref_rel_hold_dr_rx_read_rx0 = store_thm("ref_rel_hold_dr_rx_read_rx0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_read_rx0) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
?ds_abs1'.(ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_read dr with dr_last_read_v := SOME v), spi'))``,
rw [spi_tr_cases, dr_read_def, dr_read_rx0_def, read_SPI_regs_state_def,
read_SPI_regs_value_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`ds_abs1.state = abs1_rx_read` by METIS_TAC [dr_rx_read_rx0_imply_abs1_rx_ready] >>
`spi.state = rx_data_ready` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
EXISTS_TAC ``comb_abs1_rx_operations ds_abs1`` >>
rw [COMB_ABS1_RX_ENABLE_def, read_SPI_regs_def, SPI0_RX0_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, SPI0_CH0STAT_def, SPI0_CH0CTRL_def,
SPI0_TX0_def, SPI0_RX0_def, comb_abs1_rx_operations_def, 
comb_abs1_rx_read_op_def, read_RX0_def] >-
(fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []) >>
fs [ref_rel_def, CHECK_RXS_BIT_def]);

(* relation holds when driver state is dr_rx_read_conf *)
val ref_rel_hold_dr_rx_read_conf = store_thm("ref_rel_hold_dr_rx_read_conf",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_rx_read_conf) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);

(* relation holds when driver state is dr_xfer_idle *)
val ref_rel_hold_dr_xfer_idle = store_thm("ref_rel_hold_dr_xfer_idle",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_idle) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);


(* relation holds when driver state is dr_xfer_read_txs *)
val ref_rel_hold_dr_xfer_read_txs = store_thm("ref_rel_hold_dr_xfer_read_txs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_read_txs) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0stat_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_CH0STAT_def, SPI0_PA_RANGE_def, SPI0_START_def,
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def,
SPI0_CH0CONF_def, build_CH0STAT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0STAT_def] >>
Cases_on `spi.state` >> rw [] >> 
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []);

(* relation holds when driver state is dr_xfer_read_rxs *)
val ref_rel_hold_dr_xfer_read_rxs = store_thm("ref_rel_hold_dr_xfer_read_rxs",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_read_rxs) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0stat_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_CH0STAT_def, SPI0_PA_RANGE_def, SPI0_START_def,
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def,
SPI0_CH0CONF_def, build_CH0STAT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0STAT_def] >>
Cases_on `spi.state` >> rw [] >> 
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [] >>
EVAL_TAC);

(* lemma: if dr.state = dr_xfer_read_rx0, then ds_abs1.state = abs1_xfer_ready 
   according to the ref_rel *)
val dr_xfer_read_rx0_imply_abs1_xfer_ready = 
store_thm("dr_xfer_read_rx0_imply_abs1_xfer_ready",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_read_rx0) ==>
ds_abs1.state = abs1_xfer_ready``,
rw [] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
fs [IS_STATE_REL_def] >>
Cases_on `spi.state` >> rw [] >>
`(dr.state <> dr_init_pre) /\
(dr.state <> dr_init_idle) /\
(dr.state <> dr_init_read_req) /\
(dr.state <> dr_init_check_rep) /\
(dr.state <> dr_init_setting) /\
(dr.state <> dr_ready) /\
(dr.state <> dr_tx_idle) /\
(dr.state <> dr_tx_conf_issued) /\
(dr.state <> dr_tx_read_txs) /\
(dr.state <> dr_tx_check_txs) /\
(dr.state <> dr_tx_write_data) /\
(dr.state <> dr_tx_read_eot) /\
(dr.state <> dr_tx_check_eot) /\
(dr.state <> dr_tx_issue_disable) /\
(dr.state <> dr_tx_reset_conf) /\
(dr.state <> dr_rx_idle) /\
(dr.state <> dr_rx_conf_issued) /\
(dr.state <> dr_rx_read_rxs) /\
(dr.state <> dr_rx_check_rxs) /\
(dr.state <> dr_rx_read_rx0) /\
(dr.state <> dr_rx_fetch_data) /\
(dr.state <> dr_rx_issue_disable) /\
(dr.state <> dr_rx_reset_conf) /\
(dr.state <> dr_rx_sendback) /\
(dr.state <> dr_xfer_idle) /\
(dr.state <> dr_xfer_conf_issued) /\
(dr.state <> dr_xfer_read_txs) /\
(dr.state <> dr_xfer_check_txs) /\
(dr.state <> dr_xfer_write_dataO) /\
(dr.state <> dr_xfer_read_rxs) /\
(dr.state <> dr_xfer_check_rxs) /\
(dr.state <> dr_xfer_fetch_dataI) /\
(dr.state <> dr_xfer_issue_disable) /\
(dr.state <> dr_xfer_reset_conf) /\
(dr.state <> dr_tx_fetch_conf) /\
(dr.state <> dr_tx_read_conf) /\
(dr.state <> dr_rx_fetch_conf) /\
(dr.state <> dr_rx_read_conf) /\
(dr.state <> dr_xfer_fetch_conf) /\
(dr.state <> dr_xfer_read_conf) /\
(dr.state <> dr_xfer_sendback)` by rw [] >>
Cases_on `ds_abs1.state` >> rw []);

(* ds_abs1' exists and relation holds when driver state is dr_xfer_read_rx0 *)
val ref_rel_hold_dr_xfer_read_rx0 = store_thm("ref_rel_hold_dr_xfer_read_rx0",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_read_rx0) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
?ds_abs1'.(ds_abs1_tr ds_abs1 tau ds_abs1') /\
(ref_rel ds_abs1' ((dr_read dr with dr_last_read_v := SOME v), spi'))``,
rw [spi_tr_cases, dr_read_def, dr_read_rx0_def, read_SPI_regs_state_def,
read_SPI_regs_value_def, ds_abs1_tr_cases, ds_abs1_comb_tr_cases] >>
`ds_abs1.state = abs1_xfer_ready` by METIS_TAC [dr_xfer_read_rx0_imply_abs1_xfer_ready] >>
`spi.state = xfer_data_ready` by METIS_TAC [ref_rel_def, IS_STATE_REL_def] >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
rw [COMB_ABS1_XFER_ENABLE_def, read_SPI_regs_def, SPI0_RX0_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, 
SPI0_MODULCTRL_def, SPI0_CH0CONF_def, SPI0_CH0STAT_def, SPI0_CH0CTRL_def,
SPI0_TX0_def, SPI0_RX0_def, comb_abs1_xfer_operations_def, 
comb_abs1_xfer_ready_op_def, read_RX0_def] >-
(fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []) >>
fs [ref_rel_def, CHECK_RXS_BIT_def]);

(* relation holds when driver state is dr_xfer_read_conf *)
val ref_rel_hold_dr_xfer_read_conf = store_thm("ref_rel_hold_dr_xfer_read_conf",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (spi':spi_state) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (dr.state = dr_xfer_read_conf) /\
(spi_tr spi (Return (THE (dr_read dr).dr_last_read_ad) v) spi') ==>
ref_rel ds_abs1 ((dr_read dr with dr_last_read_v := SOME v), spi')``,
rw [spi_tr_cases, dr_read_def, dr_read_ch0conf_def, read_SPI_regs_state_def,
read_SPI_regs_value_def] >>
rw [read_SPI_regs_def, SPI0_SYSSTATUS_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSSTATUS_def, SPI0_SYSCONFIG_def, SPI0_CH0CONF_def, SPI0_MODULCTRL_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_CH0CONF_def] >>
Cases_on `spi.state` >> rw []);


(* simulation: ref_rel holds for ds_abs1 or ds_abs1' when driver and controller perform READ and RETURN operations *)
val comb_abs1_hold_ref_rel_RD_RE = store_thm("comb_abs1_hold_ref_rel_RD_RE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (dr':driver_state)
(spi':spi_state) (a:word32) (v:word32).
(ref_rel ds_abs1 (dr, spi)) /\ (driver_tr dr (Read a v) dr') /\ 
(spi_tr spi (Return a v) spi') ==>
(ref_rel ds_abs1 (dr', spi')) \/
(?ds_abs1'.(ds_abs1_tr ds_abs1 tau ds_abs1') /\ (ref_rel ds_abs1' (dr', spi')))``,
rw [driver_tr_cases, DR_RD_ENABLE_def] >|
[METIS_TAC [ref_rel_hold_dr_init_read_req],
METIS_TAC [ref_rel_hold_dr_tx_idle],
METIS_TAC [ref_rel_hold_dr_tx_read_txs],
METIS_TAC [ref_rel_hold_dr_tx_read_eot],
METIS_TAC [ref_rel_hold_dr_tx_read_conf],
METIS_TAC [ref_rel_hold_dr_rx_idle],
METIS_TAC [ref_rel_hold_dr_rx_read_rxs],
METIS_TAC [ref_rel_hold_dr_rx_read_rx0],
METIS_TAC [ref_rel_hold_dr_rx_read_conf],
METIS_TAC [ref_rel_hold_dr_xfer_idle],
METIS_TAC [ref_rel_hold_dr_xfer_read_txs],
METIS_TAC [ref_rel_hold_dr_xfer_read_rxs],
METIS_TAC [ref_rel_hold_dr_xfer_read_rx0],
METIS_TAC [ref_rel_hold_dr_xfer_read_conf]]);

val _ = export_theory();
