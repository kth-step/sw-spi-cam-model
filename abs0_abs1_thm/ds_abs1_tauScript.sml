open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory;

val _ = new_theory "ds_abs1_tau";

(* Theorem: for most states with tau transitions,
   tau is the only possible transition label *)
val ds_abs1_only_tau = store_thm("ds_abs1_only_tau",
``!ds_abs1 ds_abs1' ds_abs1'' lbl.
(ds_abs1.state <> abs1_tx_done_2) /\ (ds_abs1.state <> abs1_rx_fetch_data) ==>
(ds_abs1_tr ds_abs1 tau ds_abs1') ==>
(ds_abs1_tr ds_abs1 lbl ds_abs1'') ==>
lbl = tau ``,
rw [ds_abs1_tr_cases] >>
fs [ABS1_TX_LBL_ENABLE_def, ABS1_RX_LBL_ENABLE_def] >>
fs [ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def, SPI_ABS1_RX_ENABLE_def, 
SPI_ABS1_XFER_ENABLE_def, ds_abs1_dr_tr_cases,  DRIVER_ABS1_RX_ENABLE_def, 
DRIVER_ABS1_XFER_ENABLE_def, ds_abs1_comb_tr_cases, COMB_ABS1_INIT_ENABLE_def, 
COMB_ABS1_TX_ENABLE_def, COMB_ABS1_RX_ENABLE_def, COMB_ABS1_XFER_ENABLE_def]);

(* For some states that have tau transitions, there is only 1 possible next state*)
val ds_abs1_only_1_state_if_tau = store_thm("ds_abs1_only_1_state_if_tau",
``!ds_abs1 ds_abs1' ds_abs1''.
(ds_abs1_tau_only_1_state ds_abs1) ==>
(ds_abs1_tr ds_abs1 tau ds_abs1') ==>
(ds_abs1_tr ds_abs1 tau ds_abs1'') ==>
ds_abs1' = ds_abs1''``,
rw [ds_abs1_tr_cases, ds_abs1_tau_only_1_state_def] >>
Cases_on `ds_abs1.state` >>
rw [] >>
fs [ds_abs1_spi_tr_cases, SPI_ABS1_TX_ENABLE_def, SPI_ABS1_RX_ENABLE_def, 
SPI_ABS1_XFER_ENABLE_def, ds_abs1_dr_tr_cases,  DRIVER_ABS1_RX_ENABLE_def, 
DRIVER_ABS1_XFER_ENABLE_def, ds_abs1_comb_tr_cases, COMB_ABS1_INIT_ENABLE_def, 
COMB_ABS1_TX_ENABLE_def, COMB_ABS1_RX_ENABLE_def, COMB_ABS1_XFER_ENABLE_def] >>
rw []);

(* Theorem: for some states, tau is the only label and there is only 1 possible next state *)
val ds_abs1_only_1_state_and_tau = store_thm("ds_abs1_only_1_state_and_tau",
``!ds_abs1 ds_abs1' ds_abs1'' lbl.
(ds_abs1_tau_only_1_state ds_abs1) ==>
(ds_abs1_tr ds_abs1 tau ds_abs1') ==>
(ds_abs1_tr ds_abs1 lbl ds_abs1'') ==>
(lbl = tau) /\ (ds_abs1' = ds_abs1'')``,
rw [] >|
[METIS_TAC [ds_abs1_only_tau, ds_abs1_tau_only_1_state_def],
`lbl = tau` by METIS_TAC [ds_abs1_only_tau, ds_abs1_tau_only_1_state_def] >>
fs [] >>
METIS_TAC [ds_abs1_only_1_state_if_tau]]);

(*
only_1_tau tr s1 s2 equal
 tr s1 tau s2 and
 !lbl2 s3 . tr s1 lbl2 S3 ==>
  s1 equal S3
   and lbl2 equal tau  
 !lbl4 s4 . tr s4 lbl4 s2 implies
  lbl4 equal tau 

simplify tr1 tr2 s1 s2 define as



Hol_reln simplify tr s1 s2 
only_1_tau tr s1 s2 and exists lbl s3. tr s2 lbl s3
  then simplify tr s1 lbl s3
only_1_tau tr s1 s2 and exists s3. tr s3 tau s2
  then simplify tr s3 lbl s1
!s3 s4. s1 neq s3 and s1 neq s4 and tr s3 lbl s4 then
 simplify tr s3 lbl s4
*)


val _ = export_theory();
