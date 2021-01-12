open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "ds_abs1_tau_only";

(* Theorem: ds_abs1_tau only for most states with tau transitions *)
val ds_abs1_tau_only = store_thm("ds_abs1_tau_only",
``!ds_abs1 ds_abs1' ds_abs1'' lbl.
(ds_abs1.state <> abs1_tx_done_2) /\ (ds_abs1.state <> abs1_rx_fetch_data) ==>
(ds_abs1_tr ds_abs1 tau ds_abs1') ==>
(ds_abs1_tr ds_abs1 lbl ds_abs1'') ==>
lbl = tau``,
rw [ds_abs1_tr_cases] >>
fs [ABS1_TX_LBL_ENABLE_def, ABS1_RX_LBL_ENABLE_def] >>
fs [ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def, SPI_ABS1_RX_ENABLE_def, 
SPI_ABS1_XFER_ENABLE_def, ds_abs1_dr_tr_cases,  DRIVER_ABS1_RX_ENABLE_def, 
DRIVER_ABS1_XFER_ENABLE_def, ds_abs1_comb_tr_cases, COMB_ABS1_INIT_ENABLE_def, 
COMB_ABS1_TX_ENABLE_def, COMB_ABS1_RX_ENABLE_def, COMB_ABS1_XFER_ENABLE_def]);

val _ = export_theory();
