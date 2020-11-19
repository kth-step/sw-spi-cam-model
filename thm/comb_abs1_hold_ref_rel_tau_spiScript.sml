open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory SPI_initTheory SPI_schedulerTheory;
open driver_stateTheory driver_relationTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory;
open ref_relTheory;


val _ = new_theory "comb_abs1_hold_ref_rel_tau_spi";

(* have to assume dr.init.state <> dr_init_idle *)
val ABS1_IMP_SPI_INIT_ENABLE = store_thm("ABS1_IMP_SPI_INIT_ENABLE",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (SPI_ABS1_INIT_ENABLE ds_abs1) ==>
(INIT_ENABLE spi)``,
rw [] >>
FULL_SIMP_TAC std_ss [SPI_ABS1_INIT_ENABLE_def, INIT_ENABLE_def] >>
`IS_INIT_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def] >>
rw [] >>
cheat);

val ref_rel_tau_spi_init = store_thm ("ref_rel_tau_spi_init",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (SPI_ABS1_INIT_ENABLE ds_abs1) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (spi_abs1_init_operations ds_abs1) dr' spi')``,
rw [local_tr_cases, spi_tr_cases] >>
EXISTS_TAC ``dr:driver_state`` >>
EXISTS_TAC ``spi_init_operations spi`` >>
`INIT_ENABLE spi` by METIS_TAC [ABS1_IMP_SPI_INIT_ENABLE] >>
FULL_SIMP_TAC std_ss [SPI_ABS1_INIT_ENABLE_def, INIT_ENABLE_def] >>
rw [spi_abs1_init_operations_def, spi_init_operations_def, 
spi_abs1_init_start_op_def, init_reset_op_def] >>
FULL_SIMP_TAC std_ss [ref_rel_def] >>
rw [] >>
FULL_SIMP_TAC std_ss [IS_INIT_REL_def, IS_TX_REL_def, IS_RX_REL_def, IS_XFER_REL_def] >>
rw []);


val comb_abs1_hold_ref_rel_tau_spi = store_thm("comb_abs1_hold_ref_rel_tau_spi",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state).
(ref_rel ds_abs1 dr spi) /\ (ds_abs1_spi_tr ds_abs1 tau_spi ds_abs1') ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' dr' spi')``,
rw [ds_abs1_spi_tr_cases] >|
rw [ref_rel_tau_spi_init],


);

val _ = export_theory();
