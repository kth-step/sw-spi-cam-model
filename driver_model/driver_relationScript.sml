open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open driver_stateTheory SPI_stateTheory driver_checkTheory driver_writeTheory driver_readTheory;

val _ = new_theory "driver_relation";

(* dr_write_address: driver_state -> word32 option *)
val dr_write_address_def = Define `
dr_write_address (dr:driver_state) =
let (ad, v, dr') = dr_write dr in ad`

(* dr_write_value: driver_state -> word32 option *)
val dr_write_value_def = Define `
dr_write_value (dr:driver_state) =
let (ad, v, dr') = dr_write dr in v`

(* dr_write_state: driver_state -> driver_state *)
val dr_write_state_def = Define `
dr_write_state (dr:driver_state) =
let (ad, v, dr') = dr_write dr in dr'`

(* dr_read_address: driver_state -> word32 option *)
val dr_read_address_def = Define `
dr_read_address (dr:driver_state) =
let (ad, dr') = dr_read dr in ad`

(* dr_read_state: driver_state -> driver_state *)
val dr_read_state_def = Define `
dr_read_state (dr:driver_state) =
let (ad, dr') = dr_read dr in dr'`

val (driver_tr_rules, driver_tr_ind, driver_tr_cases) = Hol_reln `
(!(dr:driver_state). T ==> driver_tr dr (Check a v) (dr_check dr a v)) /\
(!(dr:driver_state). ((INIT_WR_ENABLE dr) \/ (TX_WR_ENABLE dr) \/ (RX_WR_ENABLE dr) \/ 
(XFER_WR_ENABLE dr)) /\ (dr_write_address dr <> NONE) /\ (dr_write_value dr <> NONE) ==> 
driver_tr dr (Write (THE (dr_write_address dr)) (THE (dr_write_value dr))) (dr_write_state dr)) /\
(!(dr:driver_state). ((INIT_RD_ENABLE dr) \/ (TX_RD_ENABLE dr) \/ (RX_RD_ENABKE dr) \/
(XFER_RD_ENABLE dr)) /\ (dr_read_address dr <> NONE) ==> 
driver_tr dr (Read (THE (dr_read_address dr))) (dr_read_state dr))`


val _ = export_theory();
