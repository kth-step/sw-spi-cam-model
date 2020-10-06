open HolKernel bossLib boolLib Parse;
open spi_absstateTheory spi_abslblTheory write_absregsTheory read_absregsTheory;
open SPI_stateTheory

val _ = new_theory "spi_abs_rel";

val read_abs_spi_regs_value_def = Define `
read_abs_spi_regs_value (env:environment) (pa:word32) (spi_abs:spi_abs_state) =
let (spi_abs', v) = read_abs_spi_regs env pa spi_abs in v`

val read_abs_spi_regs_state_def = Define `
read_abs_spi_regs_state (env:environment) (pa:word32) (spi_abs:spi_abs_state) =
let (spi_abs', v) = read_abs_spi_regs env pa spi_abs in spi_abs'`

val tx_abs_trans_done_op_state_def = Define `
tx_abs_trans_done_op_state (spi_abs:spi_abs_state) =
let (spi_abs', v_option) = tx_abs_trans_done_op spi_abs in spi_abs'`

val tx_abs_trans_done_op_value_def = Define `
tx_abs_trans_done_op_value (spi_abs:spi_abs_state) =
let (spi_abs', v_option) = tx_abs_trans_done_op spi_abs in v_option`

val xfer_abs_exchange_data_op_state_def = Define `
xfer_abs_exchange_data_op_state (spi_abs:spi_abs_state) (dataIN:word8 option) =
let (spi_abs', v_option) = xfer_abs_exchange_data_op spi_abs dataIN in spi_abs'`

val xfer_abs_exchange_data_op_value_def = Define `
xfer_abs_exchange_data_op_value (spi_abs:spi_abs_state) (dataIN:word8 option) =
let (spi_abs', v_option) = xfer_abs_exchange_data_op spi_abs dataIN in v_option`

(* relation for spi_abs state transition *)
val (spi_abs_tr_rules, spi_abs_tr_ind, spi_abs_tr_cases) = Hol_reln `
(!(spi_abs:spi_abs_state). T ==> 
spi_abs_tr spi_abs (Update a v) (write_abs_spi_regs a v spi_abs)) /\
(!(spi_abs:spi_abs_state). T ==>
SPI_abs_tr spi_abs (Return a (read_abs_spi_regs_value env a spi_abs)) (read_abs_spi_regs_state env a spi_abs)) /\
(!(spi_abs:spi_abs_state). 
(spi_abs.tx.state = abs_tx_trans_done) /\ (spi_abs.regs.CH0STAT.TXS = 1w) ==>
spi_abs_tr spi_abs (TX (tx_abs_trans_done_op_value spi_abs)) (tx_abs_trans_done_op_state spi_abs)) /\
(!(spi_abs:spi_abs_state). 
(spi_abs.rx.state = abs_rx_receive_data) /\ (spi_abs.regs.CH0STAT.RXS = 0w) ==>
spi_abs_tr spi_abs (RX data) (rx_abs_receive_data_op spi_abs data)) /\
(!(spi_abs:spi_abs_state). 
(spi_abs.xfer.state =abs_xfer_exchange_data) /\ (spi_abs.regs.CH0STAT.TXS = 1w) /\ 
(spi_abs.regs.CH0STAT.RXS = 0w) ==>
spi_abs_tr spi_abs (XFER dataIN (xfer_abs_exchange_data_op_value spi_abs dataIN)) (xfer_abs_exchange_data_op_state spi_abs dataIN))`

val _ = export_theory();
