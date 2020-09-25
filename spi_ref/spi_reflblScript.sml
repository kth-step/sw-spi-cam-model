open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open spi_refstateTheory;

(* Define spi_ref internal operations with labels TX, RX and XFER *)
val _ = new_theory "spi_reflbl"

(* tx_ref_trans_done_op: spi_ref_state -> spi_ref_state * word8 option *)
val tx_ref_trans_done_op_def = Define `
tx_ref_trans_done_op (spi_ref:spi_ref_state) =
if (spi_ref.tx.state = ref_tx_trans_done) /\ (spi_ref.regs.CH0STAT.TXS = 1w) then
(spi_ref with <|regs := spi_ref.regs 
with CH0STAT := spi_ref.regs.CH0STAT with EOT := 1w;
tx := spi_ref.tx with state := ref_tx_ready_for_trans |>,
SOME spi_ref.TX_SHIFT_REG)
else if (spi_ref.tx.state = ref_tx_trans_done) /\ (spi_ref.regs.CH0STAT.TXS = 0w)
then (spi_ref with err := T, NONE)
else (spi_ref, NONE)`

(* rx_ref_receive_data_op: spi_ref_state -> word8 option -> spi_ref_state *)
val rx_ref_receive_data_op_def = Define `
rx_ref_receive_data_op (spi_ref:spi_ref_state) (data:word8 option) =
if (spi_ref.rx.state = ref_rx_receive_data) /\ (spi_ref.regs.CH0STAT.RXS = 0w)
/\ (data <> NONE) then
spi_ref with <|RX_SHIFT_REG := THE data;
regs := spi_ref.regs with <| RX0 := w2w (THE data);
CH0STAT := spi_ref.regs.CH0STAT with RXS := 1w |>;
rx := spi_ref.rx with state := ref_rx_data_ready |>
else spi_ref`

(* xfer_ref_exchange_data_op: spi_ref_state -> word8 option -> spi_ref_state * word8 option *)
val xfer_ref_exchange_data_op_def = Define `
xfer_ref_exchange_data_op (spi_ref:spi_ref_state) (dataIN:word8 option) =
if (spi_ref.xfer.state = ref_xfer_exchange_data) 
/\ (spi_ref.regs.CH0STAT.RXS = 0w) /\ (dataIN <> NONE) then
(spi_ref with <|regs := spi_ref.regs
with <|CH0STAT := spi_ref.regs.CH0STAT with <|EOT := 1w; RXS := 1w|>;
RX0 := w2w (THE dataIN) |>;
RX_SHIFT_REG := THE dataIN;
xfer := spi_ref.xfer with state := ref_xfer_data_ready |>,
SOME spi_ref.TX_SHIFT_REG)
else (spi_ref, NONE)`

val _ = export_theory();
