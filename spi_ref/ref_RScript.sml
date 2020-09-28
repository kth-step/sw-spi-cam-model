open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;
open spi_refstateTheory;

val _ = new_theory "ref_R";

(* spi registers partial equivalence: regs hava the same value
 * except SYSSTATUS and CH0STAT.
 * spi_regs_part_eq: spi_regs -> spi_regs -> bool
 *)
val spi_regs_part_eq_def = Define `
spi_regs_part_eq (regs1:spi_regs) (regs2:spi_regs) =
((regs1.SYSCONFIG = regs2.SYSCONFIG) /\ (regs1.MODULCTRL = regs2.MODULCTRL) /\
(regs1.CH0CONF = regs2.CH0CONF) /\ (regs1.CH0CTRL = regs2.CH0CTRL) /\
(regs1.TX0 = regs2.TX0) /\ (regs1.RX0 = regs2.RX0))`

(* IS_INIT_REL: ref_init_state -> init_state -> bool  *)
val IS_INIT_REL_def = Define `
IS_INIT_REL (ref_init:ref_init_state) (init:init_state) =
((((ref_init.state = ref_init_start) /\ (init.state = init_start)) \/
((ref_init.state = ref_init_setregs) /\ (init.state = init_reset \/ init.state = init_setregs)) \/
((ref_init.state = ref_init_done) /\ (init.state = init_done))) /\
(ref_init.sysconfig_mode_done = init.sysconfig_mode_done) /\
(ref_init.modulctrl_bus_done = init.modulctrl_bus_done) /\
(ref_init.ch0conf_wordlen_done = init.ch0conf_wordlen_done) /\
(ref_init.ch0conf_mode_done = init.ch0conf_mode_done) /\
(ref_init.ch0conf_speed_done = ref_init.ch0conf_speed_done))`

(* IS_TX_REL: ref_tx_state -> tx_state -> bool *)
val IS_TX_REL_def = Define `
IS_TX_REL (ref_tx:ref_tx_state) (tx:tx_state) =
((ref_tx.state = ref_tx_idle /\ tx.state = tx_idle) \/
(ref_tx.state = ref_tx_conf_ready /\ tx.state = tx_conf_ready) \/
(ref_tx.state = ref_tx_ready_for_trans /\ (tx.state = tx_channel_enabled \/
tx.state = tx_ready_for_trans)) \/
(ref_tx.state = ref_tx_trans_done /\ (tx.state = tx_trans_data \/ tx.state = tx_trans_done \/ tx.state = tx_trans_check)) \/
(ref_tx.state = ref_tx_channel_disabled /\ tx.state = tx_channel_disabled))`

(* IS_RX_REL: ref_rx_state -> rx_state -> bool *)
val IS_RX_REL_def = Define `
IS_RX_REL (ref_rx:ref_rx_state) (rx:rx_state) =
((ref_rx.state = ref_rx_idle /\ rx.state = rx_idle) \/
(ref_rx.state = ref_rx_conf_ready /\ rx.state = rx_conf_ready) \/
(ref_rx.state = ref_rx_receive_data /\ (rx.state = rx_channel_enabled \/
rx.state = rx_receive_data)) \/
(ref_rx.state = ref_rx_data_ready /\ (rx.state = rx_update_RX0 \/ 
rx.state = rx_data_ready \/ rx.state = rx_receive_check)) \/
(ref_rx.state = ref_rx_channel_disabled /\ rx.state = rx_channel_disabled))`

(* IS_XFER_REL: ref_xfer_state -> xfer_state -> bool *)
val IS_XFER_REL_def = Define `
IS_XFER_REL (ref_xfer:ref_xfer_state) (xfer:xfer_state) =
((ref_xfer.state = ref_xfer_idle /\ xfer.state = xfer_idle) \/
(ref_xfer.state = ref_xfer_conf_ready /\ xfer.state = xfer_conf_ready) \/
(ref_xfer.state = ref_xfer_ready_for_trans /\ (xfer.state = xfer_channel_enabled
\/ xfer.state = xfer_ready_for_trans)) \/
(ref_xfer.state = ref_xfer_exchange_data /\ (xfer.state = xfer_trans_data \/
xfer.state = xfer_exchange_data)) \/
(ref_xfer.state = ref_xfer_data_ready /\ (xfer.state = xfer_update_RX0 \/
xfer.state = xfer_data_ready \/ xfer.state = xfer_check)) \/
(ref_xfer.state = ref_xfer_channel_disabled /\ xfer.state = xfer_channel_disabled))`

(* a refinement relation R for spi_ref and spi 
 * refine_R: spi_ref_state -> spi_state -> bool
 *)
val refine_R_def = Define `
refine_R (spi_ref:spi_ref_state) (spi:spi_state) = 
((spi_regs_part_eq spi_ref.regs spi.regs) /\ (spi_ref.err = spi.err) /\
(IS_INIT_REL spi_ref.init spi.init) /\ (IS_TX_REL spi_ref.tx spi.tx) /\
(IS_RX_REL spi_ref.rx spi.rx) /\ (IS_XFER_REL spi_ref.xfer spi.xfer))`

val _ = export_theory();
