open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory SPI_relationTheory write_SPIregsTheory read_SPIregsTheory SPI_initTheory SPI_schedulerTheory SPI_txTheory SPI_rxTheory SPI_xferTheory SPI_tracesTheory;

val _ = new_theory "spi_tr_thm";

val spi_tr_with_state_err = store_thm("spi_tr_with_state_err",
``spi_invariant spi_tr spi_err_check``,
rw [spi_invariant_def, spi_tr_cases] >|

[FULL_SIMP_TAC (std_ss++WORD_ss) [spi_err_check_def, write_SPI_regs_def],

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
