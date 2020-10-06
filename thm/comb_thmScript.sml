open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open SPI_relationTheory SPI_rxTheory SPI_txTheory SPI_schedulerTheory SPI_stateTheory;
open write_SPIregsTheory board_memTheory;

val _ = new_theory "comb_thm";

(* For an SPI device in a good state, if driver updates the TX0 with a value,
 * then spi.regs.TX0 = data
 *)
val spi_tx_update_TX0 = store_thm("spi_tx_update_TX0",
``!spi d.
(spi.tx.state = tx_ready_for_trans) /\
(spi.init.state = init_done) /\ (spi.rx.state = rx_idle) /\
(spi.xfer.state = xfer_idle) /\ (~ spi.err) /\
(spi.regs.CH0STAT.TXS = 1w) /\ (spi.regs.CH0CONF.WL = 7w) /\ 
(spi' = write_SPI_regs SPI0_TX0 d spi) ==>
(spi_tr spi (Update SPI0_TX0 d) spi') /\
(spi'.tx.state = tx_trans_data) /\
(spi'.regs.TX0 = (7 >< 0) d) /\
(spi'.init.state = init_done) /\
(spi'.rx.state = rx_idle) /\
(spi'.xfer.state = xfer_idle)``,
rw [spi_tr_cases, write_SPI_regs_def, SPI0_TX0_def, SPI0_PA_RANGE_def, 
SPI0_START_def, SPI0_END_def,SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, 
SPI0_CH0CONF_def, SPI0_CH0CTRL_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss) [write_TX0_def, CHECK_TXS_BIT_def, LET_DEF] >>
EVAL_TAC >>
rw []);

(* The SPI device performs interal tx automaton, 
 * to send the value from TX0 to SHIFT register.
 *)
val spi_tx_SHIFT_TX0 = store_thm("spi_tx_SHIFT_TX0",
``!spi.(spi.tx.state = tx_trans_data) /\ (spi.init.state = init_done) 
/\ (spi.rx.state = rx_idle) /\ (spi.xfer.state = xfer_idle) ==>
?spi'.(spi_tr spi tau spi') /\ (spi'.TX_SHIFT_REG = w2w spi.regs.TX0)``,
rw [spi_tr_cases] >>
EXISTS_TAC ``(spi_tx_operations spi)`` >>
rw [TX_ENABLE_def] >>
rw [spi_tx_operations_def, tx_trans_data_op_def]);

(* combine 2 steps *)
val spi_tx_SHIFT_eq_d = store_thm("spi_tx_SHIFT_eq_d",
``!spi d.
(spi.tx.state = tx_ready_for_trans) /\
(spi.init.state = init_done) /\ (spi.rx.state = rx_idle) /\
(spi.xfer.state = xfer_idle) /\ (~ spi.err) /\
(spi.regs.CH0STAT.TXS = 1w) /\ (spi.regs.CH0CONF.WL = 7w) ==>
?spi' spi''. (spi_tr spi (Update SPI0_TX0 d) spi') /\ 
(spi_tr spi' tau spi'') /\ 
(spi''.TX_SHIFT_REG = w2w ((7 >< 0) d:word32))``,
REPEAT STRIP_TAC >>
EXISTS_TAC ``write_SPI_regs SPI0_TX0 d spi`` >>
rw [RIGHT_EXISTS_AND_THM] >|
[rw [spi_tr_cases], 
`(write_SPI_regs SPI0_TX0 d spi).tx.state = tx_trans_data` 
by METIS_TAC[spi_tx_update_TX0] >>
`(write_SPI_regs SPI0_TX0 d spi).init.state = init_done` 
by METIS_TAC[spi_tx_update_TX0] >>
`(write_SPI_regs SPI0_TX0 d spi).rx.state = rx_idle` 
by METIS_TAC[spi_tx_update_TX0] >>
`(write_SPI_regs SPI0_TX0 d spi).xfer.state = xfer_idle` 
by METIS_TAC[spi_tx_update_TX0] >>
`(7 >< 0) d = (write_SPI_regs SPI0_TX0 d spi).regs.TX0` 
by METIS_TAC[spi_tx_update_TX0] >>
METIS_TAC [spi_tx_SHIFT_TX0]]);

(* data for one spi.TX_SHIFT_REG -> the other spi.RX_SHIFT_REG *)
val spi_tr_RX_shift = store_thm("spi_tr_RX_shift",
``!spi d. (spi_tr spi (RX (SOME d)) spi')
==> spi'.RX_SHIFT_REG = d``,
rw [spi_tr_cases] >>
ASM_SIMP_TAC std_ss [rx_receive_data_op_def] >>
rw []);

val spi_tr_TX_shift = store_thm("spi_tr_TX_shift",
``!spi d. (spi_tr spi (TX (SOME d)) spi')
==> d = spi.TX_SHIFT_REG``,
rw [spi_tr_cases] >>
FULL_SIMP_TAC std_ss [tx_trans_done_op_value_def,tx_trans_done_op_def,LET_DEF]);

val spi_comb_TX_RX = store_thm("spi_comb_TX_RX",
``!spi1 spi2 d.(spi_tr spi1 (TX (SOME d)) spi1') /\ 
(spi_tr spi2 (RX (SOME d)) spi2') ==>
(spi_cb_tr (spi1, spi2) (spi1', spi2')) /\ (spi2'.RX_SHIFT_REG = spi1.TX_SHIFT_REG)``,
REPEAT STRIP_TAC >|
[ASM_SIMP_TAC std_ss [spi_cb_tr_cases] >>
METIS_TAC[],
METIS_TAC[spi_tr_RX_shift,spi_tr_TX_shift]]);

(* 2 SPI devices: after some steps, spi2.rx0 = spi1.tx0, data transferred *)
val spi_comb_data_trans = store_thm("spi_comb_data_trans",
``!spi1 spi2.
(spi1.tx.state = tx_trans_data) /\ (spi1.init.state = init_done) /\
(spi1.rx.state = rx_idle) /\ (spi1.xfer.state = xfer_idle) /\
(spi2.rx.state = rx_receive_data) /\ (spi2.init.state = init_done) /\
(spi2.tx.state = tx_idle) /\ (spi2.xfer.state = xfer_idle) /\
(spi2.regs.CH0STAT.RXS = 0w)
==> ?spi1' spi1'' spi2' spi2''.(spi_cb_tr (spi1,spi2) (spi1',spi2)) /\
(spi_cb_tr (spi1',spi2) (spi1'', spi2')) /\
(spi_cb_tr (spi1'',spi2') (spi1'',spi2'')) /\
(spi2''.regs.RX0 = w2w (w2w spi1.regs.TX0:word8))``,
REPEAT STRIP_TAC >>
EXISTS_TAC ``spi_tx_operations spi1`` >>
rw [RIGHT_EXISTS_AND_THM] >| 
[`TX_ENABLE spi1` by rw [TX_ENABLE_def] >>
`spi_tr spi1 tau (spi_tx_operations spi1)` by METIS_TAC[spi_tr_cases] >>
rw [spi_cb_tr_cases],
rw [spi_tx_operations_def] >>
`(tx_trans_data_op spi1).tx.state = tx_trans_done` 
by rw [tx_trans_data_op_def] >>
`(tx_trans_data_op spi1).regs.CH0STAT.TXS = 1w` 
by rw [tx_trans_data_op_def] >>
`spi_tr (tx_trans_data_op spi1) (TX (tx_trans_done_op_value (tx_trans_data_op spi1))) (tx_trans_done_op_state (tx_trans_data_op spi1))` by rw [spi_tr_cases] >>
EXISTS_TAC ``tx_trans_done_op_state (tx_trans_data_op spi1)`` >>
EXISTS_TAC 
``rx_receive_data_op spi2 (tx_trans_done_op_value (tx_trans_data_op spi1))`` >>
rw [] >| 
[`spi_tr spi2 (RX (tx_trans_done_op_value
 (tx_trans_data_op spi1))) (rx_receive_data_op spi2 
(tx_trans_done_op_value (tx_trans_data_op spi1)))` by rw [spi_tr_cases] >>
METIS_TAC [spi_cb_tr_cases],
EXISTS_TAC ``spi_rx_operations (rx_receive_data_op spi2 
(tx_trans_done_op_value (tx_trans_data_op spi1)))`` >>
`(tx_trans_done_op_value (tx_trans_data_op spi1)) <> NONE` by 
rw [tx_trans_done_op_value_def, tx_trans_done_op_def, tx_trans_data_op_def] >>
`(rx_receive_data_op spi2 (tx_trans_done_op_value (tx_trans_data_op spi1))).rx.state = rx_update_RX0` by rw [rx_receive_data_op_def] >>
`(rx_receive_data_op spi2 (tx_trans_done_op_value (tx_trans_data_op spi1))).init.state = init_done` by rw [rx_receive_data_op_def] >>
`(rx_receive_data_op spi2 (tx_trans_done_op_value (tx_trans_data_op spi1))).tx.state = tx_idle` by rw [rx_receive_data_op_def] >>
`(rx_receive_data_op spi2 (tx_trans_done_op_value (tx_trans_data_op spi1))).xfer.state = xfer_idle` by rw [rx_receive_data_op_def] >>
`spi_tr (rx_receive_data_op spi2 (tx_trans_done_op_value 
(tx_trans_data_op spi1))) tau (spi_rx_operations 
(rx_receive_data_op spi2 (tx_trans_done_op_value 
(tx_trans_data_op spi1))))` by rw [spi_tr_cases, RX_ENABLE_def] >>
rw [spi_cb_tr_cases] >>
rw [spi_rx_operations_def,rx_update_RX0_op_def,rx_receive_data_op_def,
tx_trans_done_op_value_def,tx_trans_done_op_def,tx_trans_data_op_def]]]);

val _ = export_theory();
