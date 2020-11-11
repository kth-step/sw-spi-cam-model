open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_relationTheory SPI_txTheory;
open driver_stateTheory;
open ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_txTheory;
open ref_relTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_trans_lbl";

(* ref_rel holds for TX label *)
val abs1_comb_hold_ref_rel_TX_lbl = store_thm("abs1_comb_hold_ref_rel_TX_lbl",
``!(spi:spi_state) (dr:driver_state) (ds_abs1:ds_abs1_state) (data:word8 option).
(ref_rel ds_abs1 dr spi) /\ (spi_tr spi (TX data) spi') ==>
?ds_abs1'. (ds_abs1_tr ds_abs1 (TX data) ds_abs1') /\ (ref_rel ds_abs1' dr spi')``,
rw [spi_tr_cases, ds_abs1_tr_cases] >|
[(* output data is equal *)
rw [tx_trans_done_op_value_def, tx_trans_done_op_def, abs1_tx_trans_done_op_value_def, abs1_tx_trans_done_op_def]
METIS_TAC[ref_rel_def],
rw [ABS1_TX_LBL_ENABLE_def] >>
`IS_TX_REL ds_abs1 dr spi` by METIS_TAC[ref_rel_def] >>
FULL_SIMP_TAC std_ss [IS_TX_REL_def] >>
rw []
]

);














val _ = export_theory();
