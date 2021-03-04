open HolKernel bossLib boolLib Parse;
open SPI_stateTheory ds_abs1_stateTheory weak_bisimulationTheory ds_abs0_relTheory abs_relTheory ds_abs0_xferTheory ds_abs1_relTheory ds_abs1_xferTheory;

val _ = new_theory "abs_rel_holds_XFER_lbl";

(* abs_rel holds when ds_abs1 performs XFER label transition *)
val abs_rel_holds_abs1_XFER_lbl = store_thm("abs_rel_holds_abs1_XFER_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs1.state = abs1_xfer_exchange) /\ (dataIN <> NONE) ==>
?ds_abs0'. ds_abs0_tr ds_abs0 (XFER dataIN (abs1_xfer_exchange_op_value ds_abs1 dataIN)) ds_abs0' /\ 
abs_rel ds_abs0' (abs1_xfer_exchange_op_state ds_abs1 dataIN)``,
rw [abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_state_def,
abs1_xfer_exchange_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs0.state = abs0_xfer_idle` by METIS_TAC [IS_ABS_STATE_REL_def] >>
rw [ds_abs0_tr_cases, abs0_xfer_op_value_def, abs0_xfer_op_state_def, abs0_xfer_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]);

(* abs_rel holds when ds_abs0 performs XFER label transition *)
val abs_rel_holds_abs0_XFER_lbl = store_thm("abs_rel_holds_abs0_XFER_lbl",
``!(ds_abs0:ds_abs0_state) (ds_abs1:ds_abs1_state) (dataIN:word8 option).
(abs_rel ds_abs0 ds_abs1) /\ (ds_abs0.state = abs0_xfer_idle) /\ (dataIN <> NONE) ==>
(?ds_abs1'. ds_abs1_tr ds_abs1 (XFER dataIN (abs0_xfer_op_value ds_abs0 dataIN)) ds_abs1' /\
abs_rel (abs0_xfer_op_state ds_abs0 dataIN) ds_abs1') \/
(?n ds_abs1'. (n_tau_tr n ds_abs1_tr ds_abs1 
(XFER dataIN (abs0_xfer_op_value ds_abs0 dataIN)) ds_abs1') /\
abs_rel (abs0_xfer_op_state ds_abs0 dataIN) ds_abs1')``,
rw [abs0_xfer_op_value_def, abs0_xfer_op_state_def, abs0_xfer_op_def] >>
`IS_ABS_STATE_REL ds_abs0 ds_abs1` by METIS_TAC [abs_rel_def] >>
`ds_abs1.state = abs1_xfer_exchange \/ ds_abs1.state = abs1_xfer_data \/
ds_abs1.state = abs1_xfer_prepare \/ ds_abs1.state = abs1_xfer_idle` 
by METIS_TAC [IS_ABS_STATE_REL_def] >|
[(* abs1_xfer_exchange *)
DISJ1_TAC >>
rw [ds_abs1_tr_cases, abs1_xfer_exchange_op_value_def, 
abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_xfer_data *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 0:num`` >>
rw [n_tau_tr_def, ds_abs1_tr_cases, ds_abs1_spi_tr_cases, 
SPI_ABS1_XFER_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
rw [spi_abs1_xfer_operations_def, spi_abs1_xfer_data_op_def, 
abs1_xfer_exchange_op_value_def, abs1_xfer_exchange_op_state_def,
abs1_xfer_exchange_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_xfer_prepare *)
DISJ2_TAC >>
EXISTS_TAC ``SUC 1:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC] >>
rw [ds_abs1_tr_cases, ds_abs1_comb_tr_cases, COMB_ABS1_XFER_ENABLE_def,
GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``comb_abs1_xfer_operations ds_abs1`` >>
EXISTS_TAC ``spi_abs1_xfer_operations (comb_abs1_xfer_operations ds_abs1)`` >>
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def,
ds_abs1_spi_tr_cases, SPI_ABS1_XFER_ENABLE_def, spi_abs1_xfer_operations_def,
spi_abs1_xfer_data_op_def, abs1_xfer_exchange_op_value_def,
abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def],
(* abs1_xfer_idle*)
DISJ2_TAC >>
EXISTS_TAC ``SUC 2:num`` >>
rw [n_tau_tr_def, n_tau_tr_SUC] >>
rw [ds_abs1_tr_cases, ds_abs1_spi_tr_cases, SPI_ABS1_XFER_ENABLE_def,
GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM] >>
EXISTS_TAC ``spi_abs1_xfer_operations ds_abs1`` >>
EXISTS_TAC ``comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1)`` >>
EXISTS_TAC ``spi_abs1_xfer_operations 
(comb_abs1_xfer_operations (spi_abs1_xfer_operations ds_abs1))`` >> 
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def,
ds_abs1_comb_tr_cases, COMB_ABS1_XFER_ENABLE_def, SPI_ABS1_XFER_ENABLE_def, 
spi_abs1_xfer_operations_def, spi_abs1_xfer_idle_op_def, 
spi_abs1_xfer_data_op_def, abs1_xfer_exchange_op_value_def, 
abs1_xfer_exchange_op_state_def, abs1_xfer_exchange_op_def] >>
fs [abs_rel_def, IS_ABS_STATE_REL_def]]);


val _ = export_theory();
