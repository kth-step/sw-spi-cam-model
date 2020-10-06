open HolKernel bossLib boolLib Parse;
open spi_absstateTheory;

val _ = new_theory "abs_inv";

(* spi_abs_init_invariant: spi_abs_state -> bool *)
val spi_abs_init_invariant_def = Define `
spi_abs_init_invariant (spi_abs:spi_abs_state) =
((spi_abs.init.state = abs_init_setregs) \/
(spi_abs.init.state = abs_init_done)
==> spi_abs.regs.SYSSTATUS = 1w)`

(* spi_abs_tx_invariant: spi_abs_state -> bool *)
val spi_abs_tx_invariant_def = Define `
spi_abs_tx_invariant (spi_abs:spi_abs_state) =
((spi_abs.tx.state = abs_tx_ready_for_trans \/
spi_abs.tx.state = abs_tx_trans_done \/
spi_abs.tx.state = abs_tx_channel_disabled
==> spi_abs.regs.CH0STAT.TXS = 1w) /\
(spi_abs.tx.state = abs_tx_trans_done 
==> spi_abs.regs.CH0STAT.EOT = 0w /\
spi_abs.TX_SHIFT_REG = w2w spi_abs.regs.TX0))`

(* spi_abs_rx_invariant: spi_abs_state -> bool *)
val spi_abs_rx_invariant_def = Define `
spi_abs_rx_invariant (spi_abs:spi_abs_state) =
((spi_abs.rx.state = abs_rx_receive_data \/
spi_abs.rx.state = abs_rx_channel_disabled 
==> spi_abs.regs.CH0STAT.RXS = 0w) /\ 
(spi_abs.rx.state = abs_rx_data_ready 
==> spi_abs.regs.CH0STAT.RXS = 1w /\
spi_abs.regs.RX0 = w2w spi_abs.RX_SHIFT_REG))`

(* spi_abs_xfer_invariant: spi_abs_state -> bool *)
val spi_abs_xfer_invariant_def = Define `
spi_abs_xfer_invariant (spi_abs:spi_abs_state) =
((spi_abs.xfer.state = abs_xfer_ready_for_trans \/
spi_abs.xfer.state = abs_xfer_exchange_data \/
spi_abs.xfer.state = abs_xfer_data_ready \/
spi_abs.xfer.state = abs_xfer_channel_disabled
==> spi_abs.regs.CH0STAT.TXS = 1w) /\
(spi_abs.xfer.state = abs_xfer_ready_for_trans \/
spi_abs.xfer.state = abs_xfer_exchange_data \/
spi_abs.xfer.state = abs_xfer_channel_disabled 
==> spi_abs.regs.CH0STAT.RXS = 0w) /\
(spi_abs.xfer.state = abs_xfer_data_ready 
==> spi_abs.regs.CH0STAT.RXS = 1w) /\
(spi_abs.xfer.state = abs_xfer_exchange_data 
==> spi_abs.regs.CH0STAT.EOT = 0w) /\
(spi_abs.xfer.state = abs_xfer_data_ready
==> spi_abs.regs.CH0STAT.EOT = 1w) /\
(spi_abs.xfer.state = abs_xfer_exchange_data 
==> spi_abs.TX_SHIFT_REG = w2w spi_abs.regs.TX0) /\
(spi_abs.xfer.state = abs_xfer_data_ready
==> spi_abs.regs.RX0 = w2w spi_abs.RX_SHIFT_REG))`

(* check the spi_abs.err flag to make sure spi_abs is in a defined state.
 * spi_abs_state_right:spi_abs_state -> bool*)
val spi_abs_state_right_def = Define `
spi_abs_state_right (spi_abs:spi_abs_state) = ~spi_abs.err`

(* An invariant for the spi_abs_state: 
 * this one is to help the refinement relation R. 
 * spi_abs_invariant: spi_abs_state -> bool
 *)
val spi_abs_invariant_def = Define `
spi_abs_invariant (spi_abs:spi_abs_state) =
((spi_abs_state_right spi_abs) /\
(spi_abs_init_invariant spi_abs) /\
(spi_abs_tx_invariant spi_abs) /\
(spi_abs_rx_invariant spi_abs) /\
(spi_abs_xfer_invariant spi_abs))`

val _ = export_theory();
