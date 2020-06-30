open HolKernel bossLib boolLib Parse;
open SPI_stateTheory SPI_initTheory SPI_txTheory SPI_rxTheory SPI_xferTheory;

val _ = new_theory "SPI_scheduler";

(* According to the SPI state, decide which automaton is enabled *)
val INIT_ENABLE_def = Define `
INIT_ENABLE (spi:spi_state) =
((spi.init.state = init_reset) /\ 
(spi.tx.state = tx_idle) /\
(spi.rx.state = rx_idle))`

val TX_ENABLE_def = Define `
TX_ENABLE (spi:spi_state) =
((spi.tx.state <> tx_idle) /\ (spi.tx.state <> tx_conf_ready) /\ (spi.tx.state <> tx_mem_reply)
 /\ (spi.tx.state <> tx_disable_channel) /\ (spi.tx.state <> tx_reset_conf))`

val RX_ENABLE_def = Define `
RX_ENABLE (spi:spi_state) =
(((spi.rx.state <> rx_idle) /\ (spi.rx.state <> rx_conf_ready) /\ 
(spi.rx.state <> rx_disable_channel) /\ (spi.rx.state <> rx_reset_conf)) 
\/ ((spi.rx.state = rx_idle) /\ (spi.init.state = init_done)))`

val XFER_ENABLE_def = Define `
XFER_ENABLE (spi:spi_state) =
((spi.xfer.state <> xfer_idle) /\ (spi.xfer.state <> xfer_conf_ready) /\
(spi.xfer.state <> xfer_mem_reply) /\ (spi.xfer.state <> xfer_disable_channel) 
/\ (spi.xfer.state <> xfer_reset_conf))`

(* sheduler *)
val scheduler_cases_def = Define `
(scheduler_cases Initialize (spi:spi_state) = 
(if (INIT_ENABLE spi) then init_operations spi else spi, NONE)) /\
(scheduler_cases Transmit spi = 
if (TX_ENABLE spi) then tx_operations spi else (spi,NONE)) /\
(scheduler_cases Receive spi = 
if (RX_ENABLE spi) then rx_operations spi else (spi,NONE)) /\
(scheduler_cases Transfer spi = 
if (XFER_ENABLE spi) then xfer_operations spi else (spi,NONE))`

val scheduler_def = Define `
scheduler (spi:spi_state) (env:environment) =
if spi.err then (spi, NONE)
else let (spi',r') = scheduler_cases env.scheduler spi
in (spi', r')`

val _ = export_theory();
