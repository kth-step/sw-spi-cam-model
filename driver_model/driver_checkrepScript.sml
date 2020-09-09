open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open driver_stateTheory board_memTheory;

(* Driver checks the reply from the SPI controller for a read request *)
val _ = new_theory "driver_checkrep";

(* dr_check_SYSSTATUS: driver_state -> word32 -> driver_state *)
val dr_check_SYSSTATUS_def = Define `
dr_check_SYSSTATUS (dr:driver_state) (rep_v:word32) =
let v = (0 >< 0) rep_v :word1 in
case dr.dr_init.state of
  | dr_init_idle ==> dr
  | dr_init_read_req ==> dr
  | dr_init_check_rep ==> if v = 0w 
    then dr with dr_init := dr.dr_init with state := dr_dr_check_rep
    else dr with dr_init := dr.dr_init with state := dr_dr_setting
  | dr_init_setting ==> dr
  | dr_init_done ==> dr`


val _ = export_theory();
