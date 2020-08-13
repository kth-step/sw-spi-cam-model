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
(spi_observable_lbl (Read _) = F) /\
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

val spi_tr_with_state_err = store_thm("spi_tr_with_state_err",
``spi_invariant spi_tr spi_err_check``,
rw [spi_invariant_def, spi_tr_cases] >|[
FULL_SIMP_TAC (std_ss++WORD_ss) [spi_err_check_def, write_SPI_regs_def],

FULL_SIMP_TAC (std_ss++WORD_ss) [spi_err_check_def, read_SPI_regs_state_def, read_SPI_regs_def] >>
rw [],

FULL_SIMP_TAC std_ss [spi_err_check_def, spi_init_operations_def, INIT_ENABLE_def] >>
rw [init_reset_op_def],

FULL_SIMP_TAC std_ss [spi_err_check_def, spi_tx_operations_def, TX_ENABLE_def] >>
Cases_on `s.tx.state` >>
rw [tx_channel_enabled_op_def, tx_trans_data_op_def, tx_trans_check_op_def],

FULL_SIMP_TAC std_ss [spi_err_check_def, spi_rx_operations_def, RX_ENABLE_def] >>
Cases_on `s.rx.state` >>
rw [rx_channel_enabled_op_def, rx_update_RX0_op_def, rx_receive_check_op_def],

FULL_SIMP_TAC std_ss [spi_err_check_def, spi_xfer_operations_def, XFER_ENABLE_def] >>
Cases_on `s.xfer.state` >>
rw [xfer_channel_enabled_op_def, xfer_trans_data_op_def, xfer_update_RX0_op_def,xfer_check_op_def],

FULL_SIMP_TAC std_ss [spi_err_check_def, tx_trans_done_op_state_def, tx_trans_done_op_def] >>
rw [],

FULL_SIMP_TAC std_ss [spi_err_check_def, rx_receive_data_op_def] >>
rw [],

FULL_SIMP_TAC std_ss [spi_err_check_def, xfer_exchange_data_op_state_def, xfer_exchange_data_op_def] >>
rw []]);

val _ = export_theory();
