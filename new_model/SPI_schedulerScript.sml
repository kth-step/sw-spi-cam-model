open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_initTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;

(* SPI sheduler decides the hardware internal operation steps according to its internal states *)
val _ = new_theory "SPI_scheduler";

(* X_ENABLE means X automaton is enabled for SPI internal operation *)
val INIT_ENABLE_def = Define `
INIT_ENABLE (spi:spi_state) =
((spi.init.state = init_reset) /\ 
 (spi.tx.state = tx_idle) /\
 (spi.rx.state = rx_idle) /\
 (spi.xfer.state = xfer_idle))`

val TX_ENABLE_def = Define `
TX_ENABLE (spi:spi_state) =
((spi.tx.state <> tx_idle) /\ (spi.tx.state <> tx_conf_ready) 
/\ (spi.tx.state <> tx_ready_for_trans) /\ (spi.tx.state <> tx_channel_disabled))`

val RX_ENABLE_def = Define `
RX_ENABLE (spi:spi_state) =
((spi.rx.state <> rx_idle) /\ (spi.rx.state <> rx_conf_ready) 
/\ (spi.rx.state <> rx_data_ready) /\ (spi.rx.state <> rx_channel_disabled))`

val XFER_ENABLE_def = Define `
XFER_ENABLE (spi:spi_state) =
((spi.xfer.state <> xfer_idle) /\ (spi.xfer.state <> xfer_conf_ready) 
/\ (spi.xfer.state <> xfer_ready_for_trans) /\ (spi.xfer.state <> xfer_data_ready) 
/\ (spi.xfer.state <> xfer_channel_disabled))`

(* sheduler_cases: scheduöe -> spi_state -> spi_state *)
val scheduler_cases_def = Define `
(scheduler_cases Initialize (env:environment) (spi:spi_state) = 
if (INIT_ENABLE spi) then spi_init_operations spi else spi) /\
(scheduler_cases Transmit env spi = 
if (TX_ENABLE spi) then spi_tx_operations spi else spi) /\
(scheduler_cases Receive env spi = 
if (RX_ENABLE spi) then spi_rx_operations env spi else spi) /\
(scheduler_cases Transfer env spi = 
if (XFER_ENABLE spi) then spi_xfer_operations env spi else spi)`

val spi_scheduler_def = Define `
spi_scheduler (env:environment) (spi:spi_state) =
if spi.err then spi
else 
scheduler_cases env.scheduler env spi`

val _ = export_theory();
