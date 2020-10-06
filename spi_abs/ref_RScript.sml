open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open spi_absstateTheory;

val _ = new_theory "ref_R";

(* spi registers partial equivalence: regs hava the same value
 * except SYSSTATUS and CH0STAT.
 * spi_regs_part_eq: spi_regs -> spi_regs -> bool
 *)
val spi_regs_part_eq_def = Define `
spi_regs_part_eq (regs1:spi_regs) (regs2:spi_regs) =
((regs1.SYSCONFIG = regs2.SYSCONFIG) /\ (regs1.MODULCTRL = regs2.MODULCTRL) /\
(regs1.CH0CONF = regs2.CH0CONF) /\ (regs1.CH0CTRL = regs2.CH0CTRL) /\
(regs1.TX0 = regs2.TX0))`

(* IS_INIT_REL: abs_init_state -> init_state -> bool  *)
val IS_INIT_REL_def = Define `
IS_INIT_REL (abs_init:abs_init_state) (init:init_state) =
((((abs_init.state = abs_init_start) = (init.state = init_start)) /\
((abs_init.state = abs_init_setregs) = (init.state = init_reset \/ init.state = init_setregs)) /\
((abs_init.state = abs_init_done) = (init.state = init_done))) /\
(abs_init.sysconfig_mode_done = init.sysconfig_mode_done) /\
(abs_init.modulctrl_bus_done = init.modulctrl_bus_done) /\
(abs_init.ch0conf_wordlen_done = init.ch0conf_wordlen_done) /\
(abs_init.ch0conf_mode_done = init.ch0conf_mode_done) /\
(abs_init.ch0conf_speed_done = init.ch0conf_speed_done))`

(* IS_TX_REL: abs_tx_state -> tx_state -> bool *)
val IS_TX_REL_def = Define `
IS_TX_REL (abs_tx:abs_tx_state) (tx:tx_state) =
(((abs_tx.state = abs_tx_idle) = (tx.state = tx_idle)) /\
((abs_tx.state = abs_tx_conf_ready) = (tx.state = tx_conf_ready)) /\
((abs_tx.state = abs_tx_ready_for_trans) = (tx.state = tx_channel_enabled \/
tx.state = tx_ready_for_trans \/ tx.state = tx_trans_check)) /\
((abs_tx.state = abs_tx_trans_done) = (tx.state = tx_trans_data \/ tx.state = tx_trans_done)) /\
((abs_tx.state = abs_tx_channel_disabled) = (tx.state = tx_channel_disabled)))`

(* IS_RX_REL: abs_rx_state -> rx_state -> bool *)
val IS_RX_REL_def = Define `
IS_RX_REL (abs_rx:abs_rx_state) (rx:rx_state) =
(((abs_rx.state = abs_rx_idle) = (rx.state = rx_idle)) /\
((abs_rx.state = abs_rx_conf_ready) = (rx.state = rx_conf_ready)) /\
((abs_rx.state = abs_rx_receive_data) = (rx.state = rx_channel_enabled \/
rx.state = rx_receive_data \/ rx.state = rx_receive_check)) /\
((abs_rx.state = abs_rx_data_ready) = (rx.state = rx_update_RX0 \/ 
rx.state = rx_data_ready)) /\
((abs_rx.state = abs_rx_channel_disabled) = (rx.state = rx_channel_disabled)))`

(* IS_XFER_REL: abs_xfer_state -> xfer_state -> bool *)
val IS_XFER_REL_def = Define `
IS_XFER_REL (abs_xfer:abs_xfer_state) (xfer:xfer_state) =
(((abs_xfer.state = abs_xfer_idle) = (xfer.state = xfer_idle)) /\
((abs_xfer.state = abs_xfer_conf_ready) = (xfer.state = xfer_conf_ready)) /\
((abs_xfer.state = abs_xfer_ready_for_trans) = (xfer.state = xfer_channel_enabled
\/ xfer.state = xfer_ready_for_trans \/ xfer.state = xfer_check)) /\
((abs_xfer.state = abs_xfer_exchange_data) = (xfer.state = xfer_trans_data \/
xfer.state = xfer_exchange_data)) /\
((abs_xfer.state = abs_xfer_data_ready) = (xfer.state = xfer_update_RX0 \/
xfer.state = xfer_data_ready)) /\
((abs_xfer.state = abs_xfer_channel_disabled) = (xfer.state = xfer_channel_disabled)))`

(* IS_SYSSTATUS_EQ: spi_abs_state -> spi_state -> bool *)
val IS_SYSSTATUS_EQ_def = Define `
IS_SYSSTATUS_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
((spi.init.state = init_setregs \/ spi.init.state = init_done) ==>
(spi.regs.SYSSTATUS = spi_abs.regs.SYSSTATUS))`

(* IS_TXS_EQ: spi_abs_state -> spi_state -> bool *)
val IS_TXS_EQ_def = Define `
IS_TXS_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
(((spi.tx.state = tx_ready_for_trans \/ spi.tx.state = tx_trans_done \/ 
spi.tx.state = tx_trans_check \/ spi.tx.state = tx_channel_disabled) ==>
(spi.regs.CH0STAT.TXS = spi_abs.regs.CH0STAT.TXS)) \/
((spi.xfer.state = xfer_ready_for_trans \/ spi.xfer.state = xfer_exchange_data \/
spi.xfer.state = xfer_update_RX0 \/ spi.xfer.state = xfer_data_ready \/
spi.xfer.state = xfer_check \/ spi.xfer.state = xfer_channel_disabled) ==>
(spi.regs.CH0STAT.TXS = spi_abs.regs.CH0STAT.TXS)))`

(* IS_RXS_EQ: spi_abs_state -> spi_state -> bool *)
val IS_RXS_EQ_def = Define `
IS_RXS_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
(((spi.rx.state = rx_receive_data \/ spi.rx.state = rx_data_ready \/
spi.rx.state = rx_receive_check \/ spi.rx.state = rx_channel_disabled) ==>
(spi.regs.CH0STAT.RXS = spi_abs.regs.CH0STAT.RXS)) \/
((spi.xfer.state = xfer_ready_for_trans \/ spi.xfer.state = xfer_trans_data \/
spi.xfer.state = xfer_exchange_data \/ spi.xfer.state = xfer_data_ready \/
spi.xfer.state = xfer_check \/ spi.xfer.state = xfer_channel_disabled) ==>
(spi.regs.CH0STAT.RXS = spi_abs.regs.CH0STAT.RXS)))`

(* IS_EOT_EQ: spi_abs_state -> spi_state -> bool *)
val IS_EOT_EQ_def = Define `
IS_EOT_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
(((spi.tx.state = tx_trans_done \/ spi.tx.state = tx_channel_disabled) ==>
(spi.regs.CH0STAT.EOT = spi_abs.regs.CH0STAT.EOT)) \/
((spi.xfer.state = xfer_exchange_data \/ spi.xfer.state = xfer_update_RX0 \/
spi.xfer.state = xfer_data_ready) ==>
(spi.regs.CH0STAT.EOT = spi_abs.regs.CH0STAT.EOT)))`

(* IS_RX0_EQ: spi_abs_state -> spi_state -> bool *)
val IS_RX0_EQ_def = Define `
IS_RX0_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
((spi.rx.state = rx_data_ready ==>
spi.regs.RX0 = spi_abs.regs.RX0) \/
(spi.xfer.state = xfer_data_ready ==>
spi.regs.RX0 = spi_abs.regs.RX0))`

(* TSR:TX SHIFT REGISTER.
 * IS_TSR_EQ: spi_abs_state -> spi_state -> bool
 *)
val IS_TSR_EQ_def = Define `
IS_TSR_EQ (spi_abs:spi_abs_state) (spi:spi_state) =
((spi.tx.state = tx_trans_done ==>
spi.TX_SHIFT_REG = spi_abs.TX_SHIFT_REG) \/
(spi.xfer.state = xfer_exchange_data \/ spi.xfer.state = xfer_update_RX0 \/
spi.xfer.state = xfer_data_ready ==>
spi.TX_SHIFT_REG = spi_abs.TX_SHIFT_REG))`

(* a refinement relation R for spi_abs and spi 
 * refine_R: spi_abs_state -> spi_state -> bool
 *)
val refine_R_def = Define `
refine_R (spi_abs:spi_abs_state) (spi:spi_state) = 
((spi_regs_part_eq spi_abs.regs spi.regs) /\ 
(spi_abs.err = spi.err) /\ (spi_abs.RX_SHIFT_REG = spi.RX_SHIFT_REG) /\
(IS_INIT_REL spi_abs.init spi.init) /\ (IS_TX_REL spi_abs.tx spi.tx) /\
(IS_RX_REL spi_abs.rx spi.rx) /\ (IS_XFER_REL spi_abs.xfer spi.xfer) /\
(IS_SYSSTATUS_EQ spi_abs spi) /\ (IS_TXS_EQ spi_abs spi) /\
(IS_RXS_EQ spi_abs spi) /\ (IS_EOT_EQ spi_abs spi) /\
(IS_RX0_EQ spi_abs spi) /\ (IS_TSR_EQ spi_abs spi))`

val _ = export_theory();
