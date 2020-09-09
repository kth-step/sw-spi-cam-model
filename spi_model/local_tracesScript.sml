open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib listTheory;
open SPI_stateTheory SPI_relationTheory;

val _ = new_theory "local_traces";

(* - a "local relation" is a relation for a CPU and an SPI device:
     'a # spi_state -> global_lbl_type -> 'a # spi_state -> bool
 * - an "execution" is a list of tuples of (cpu * spi) states and global lables:
     (('a # spi_state) # global_lbl_type # 'a # spi_state) list
 * - a "local execution": ('a # spi_state -> global_lbl_type -> 'a # spi_state -> bool) ->
     ((('a # spi_state) # global_lbl_type # 'a # spi_state) list) -> bool
 *)
val (local_exe_rules, local_exe_ind, local_exe_cases) = Hol_reln `
(!(cpu:'a) (spi:spi_state) (cpu':'a) (spi':spi_state) (l:global_lbl_type). 
  R (cpu,spi) l (cpu',spi') ==> local_exe R [((cpu,spi),l,(cpu',spi'))]) /\
(!(cpu1:'a) (cpu2:'a) (cpu3:'a) (spi1:spi_state) (spi2:spi_state) (spi3:spi_state) (l1:global_lbl_type) (l2:global_lbl_type).
(local_exe R (e ++ [((cpu1,spi1),l1,(cpu2,spi2))])) /\ 
(R (cpu2,spi2) l2 (cpu3,spi3)) ==>
local_exe R (e ++[((cpu1,spi1),l1,(cpu2,spi2));((cpu2,spi2),l2,(cpu3,spi3))]))`

val local_tr_for_exe_def = Define `
local_tr_for_exe = local_exe local_tr`

val local_observable_lbl_def = Define `
(local_observable_lbl tau = F) /\
(local_observable_lbl (TX _) = T) /\
(local_observable_lbl (RX _) = T) /\
(local_observable_lbl (XFER _ _) = T) /\
(local_observable_lbl (Write _ _) = F) /\
(local_observable_lbl (Update _ _) = F) /\
(local_observable_lbl (Read _) = F) /\
(local_observable_lbl (Return _ _) = F)`

(* local label trace that filter out internal operations *)
val local_trace_def = Define `
local_trace (observable:global_lbl_type -> bool) 
(t:(('a # spi_state) # global_lbl_type # 'a # spi_state) list) =
FILTER observable (MAP (FST o SND) t)`

(* get gloabl labels from the state tranistion list without filter *)
val lbl_trace_def = Define `
lbl_trace (t:(('a # spi_state) # global_lbl_type # 'a # spi_state) list) =
MAP (FST o SND) t`


val _ = export_theory();
