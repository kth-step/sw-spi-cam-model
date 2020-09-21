open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib listTheory;
open SPI_stateTheory SPI_relationTheory write_SPIregsTheory read_SPIregsTheory SPI_initTheory SPI_schedulerTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;

val _ = new_theory "SPI_traces";

(* - a "spi relation" is a relation for an SPI device, e.g. spi_tr:
     spi_state -> global_lbl_type -> spi_state -> bool
 * - an "execution" is a list of tuples of spi states and global lables:
     (spi_state # global_lbl_type # spi_state) list
 * - a "spi execution": (spi_state -> global_lbl_type -> spi_state -> bool) ->
     ((spi_state # global_lbl_type # spi_state) list) -> bool
 *)
val (spi_exe_rules, spi_exe_ind, spi_exe_cases) = Hol_reln `
(!(spi:spi_state) (spi':spi_state) (l:global_lbl_type). 
  R spi l spi' ==> spi_exe R [(spi, l, spi')]) /\
(!(spi1:spi_state) (spi2:spi_state) (spi3:spi_state) (l1:global_lbl_type) (l2:global_lbl_type).
(spi_exe R (e ++ [(spi1, l1, spi2)])) /\ 
(R spi2 l2 spi3) ==>
spi_exe R (e ++[(spi1, l1, spi2); (spi2, l2, spi3)]))`

val spi_tr_for_exe_def = Define `
spi_tr_for_exe = spi_exe spi_tr`

val spi_observable_lbl_def = Define `
(spi_observable_lbl tau = F) /\
(spi_observable_lbl (TX _) = T) /\
(spi_observable_lbl (RX _) = T) /\
(spi_observable_lbl (XFER _ _) = T) /\
(spi_observable_lbl (Write _ _) = F) /\
(spi_observable_lbl (Update _ _) = T) /\
(spi_observable_lbl (Read _ _) = F) /\
(spi_observable_lbl (Return _ _) = T)`

(* spi label trace that filter out internal operations *)
val spi_trace_def = Define `
spi_trace (observable:global_lbl_type -> bool) 
(t:(spi_state # global_lbl_type # spi_state) list) =
FILTER observable (MAP (FST o SND) t)`

(* get gloabl labels from the state tranistion list without filter *)
val spi_lbl_trace_def = Define `
spi_lbl_trace (t:(spi_state # global_lbl_type # spi_state) list) =
MAP (FST o SND) t`

val spi_invariant_def = Define `
spi_invariant (R:spi_state -> global_lbl_type -> spi_state -> bool) (P:spi_state -> bool) =
!s l s'. ((P s) /\ (R s l s')) ==> P s'`

val spi_err_check_def = Define `
spi_err_check (spi:spi_state) = spi.err`

val _ = export_theory();
