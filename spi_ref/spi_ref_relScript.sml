open HolKernel bossLib boolLib Parse;
open spi_refstateTheory spi_reflblTheory write_refregsTheory read_refregsTheory;
open SPI_stateTheory

val _ = new_theory "spi_ref_rel";

val read_ref_spi_regs_value_def = Define `
read_ref_spi_regs_value (env:environment) (pa:word32) (spi_ref:spi_ref_state) =
let (spi_ref', v) = read_ref_spi_regs env pa spi_ref in v`

val read_ref_spi_regs_state_def = Define `
read_ref_spi_regs_state (env:environment) (pa:word32) (spi_ref:spi_ref_state) =
let (spi_ref', v) = read_ref_spi_regs env pa spi_ref in spi_ref'`

val tx_ref_trans_done_op_state_def = Define `
tx_ref_trans_done_op_state (spi_ref:spi_ref_state) =
let (spi_ref', v_option) = tx_ref_trans_done_op spi_ref in spi_ref'`

val tx_ref_trans_done_op_value_def = Define `
tx_ref_trans_done_op_value (spi_ref:spi_ref_state) =
let (spi_ref', v_option) = tx_ref_trans_done_op spi_ref in v_option`

val xfer_ref_exchange_data_op_state_def = Define `
xfer_ref_exchange_data_op_state (spi_ref:spi_ref_state) (dataIN:word8 option) =
let (spi_ref', v_option) = xfer_ref_exchange_data_op spi_ref dataIN in spi_ref'`

val xfer_ref_exchange_data_op_value_def = Define `
xfer_ref_exchange_data_op_value (spi_ref:spi_ref_state) (dataIN:word8 option) =
let (spi_ref', v_option) = xfer_ref_exchange_data_op spi_ref dataIN in v_option`

(* relation for spi_ref state transition *)
val (spi_ref_tr_rules, spi_ref_tr_ind, spi_ref_tr_cases) = Hol_reln `
(!(spi_ref:spi_ref_state). T ==> 
spi_ref_tr spi_ref (Update a v) (write_ref_spi_regs a v spi_ref)) /\
(!(spi_ref:spi_ref_state). T ==>
SPI_ref_tr spi_ref (Return a (read_ref_spi_regs_value env a spi_ref)) (read_ref_spi_regs_state env a spi_ref)) /\
(!(spi_ref:spi_ref_state). (spi_ref.tx.state = ref_tx_trans_done) ==>
spi_ref_tr spi_ref (TX (tx_ref_trans_done_op_value spi_ref)) (tx_ref_trans_done_op_state spi_ref)) /\
(!(spi_ref:spi_ref_state). (spi_ref.rx.state = ref_rx_receive_data) ==>
spi_ref_tr spi_ref (RX data) (rx_ref_receive_data_op spi_ref data)) /\
(!(spi_ref:spi_ref_state). (spi_ref.xfer.state =ref_xfer_exchange_data) ==>
spi_ref_tr spi_ref (XFER dataIN (xfer_ref_exchange_data_op_value spi_ref dataIN)) (xfer_ref_exchange_data_op_state spi_ref dataIN))
(* TODO: tau transition
(!(spi_ref:spi_ref_state). (spi_ref.state = good_state_to_do_so)
==> spi_ref_tr spi_ref tau spi_ref) *)`

val _ = export_theory();
