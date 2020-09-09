open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open driver_stateTheory SPI_stateTheory;

val _ = new_theory "driver_relation";

(*
val (driver_tr_rules, driver_tr_ind, driver_tr_cases) = Hol_reln `
(!(dr:driver_state). T ==> driver_tr dr (Write (function_return_addr dr) 
(function_return_val dr)) (funtion_return_state dr)) /\
(!(dr:driver_state). T ==> driver_tr dr (Read (function_issue_addr dr))
(function_return_state dr)) /\
(!(dr:driver_state). )
`
*)

val _ = export_theory();
