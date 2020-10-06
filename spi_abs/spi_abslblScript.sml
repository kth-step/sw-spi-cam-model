open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open spi_absstateTheory;

(* Define spi_abs internal operations with labels TX, RX and XFER *)
val _ = new_theory "spi_abslbl"

(* tx_abs_trans_done_op: spi_abs_state -> spi_abs_state * word8 option *)
val tx_abs_trans_done_op_def = Define `
tx_abs_trans_done_op (spi_abs:spi_abs_state) =
if (spi_abs.tx.state = abs_tx_trans_done) /\ (spi_abs.regs.CH0STAT.TXS = 1w) then
(spi_abs with <|regs := spi_abs.regs 
with CH0STAT := spi_abs.regs.CH0STAT with EOT := 1w;
tx := spi_abs.tx with state := abs_tx_ready_for_trans |>,
SOME spi_abs.TX_SHIFT_REG)
else if (spi_abs.tx.state = abs_tx_trans_done) /\ (spi_abs.regs.CH0STAT.TXS = 0w)
then (spi_abs with err := T, NONE)
else (spi_abs, NONE)`

(* rx_abs_receive_data_op: spi_abs_state -> word8 option -> spi_abs_state *)
val rx_abs_receive_data_op_def = Define `
rx_abs_receive_data_op (spi_abs:spi_abs_state) (data:word8 option) =
if (spi_abs.rx.state = abs_rx_receive_data) /\ (spi_abs.regs.CH0STAT.RXS = 0w)
/\ (data <> NONE) then
spi_abs with <|RX_SHIFT_REG := THE data;
regs := spi_abs.regs with <| RX0 := w2w (THE data);
CH0STAT := spi_abs.regs.CH0STAT with RXS := 1w |>;
rx := spi_abs.rx with state := abs_rx_data_ready |>
else spi_abs`

(* xfer_abs_exchange_data_op: spi_abs_state -> word8 option -> spi_abs_state * word8 option *)
val xfer_abs_exchange_data_op_def = Define `
xfer_abs_exchange_data_op (spi_abs:spi_abs_state) (dataIN:word8 option) =
if (spi_abs.xfer.state = abs_xfer_exchange_data) /\ (spi_abs.regs.CH0STAT.TXS = 1w)
/\ (spi_abs.regs.CH0STAT.RXS = 0w) /\ (dataIN <> NONE) then
(spi_abs with <|regs := spi_abs.regs
with <|CH0STAT := spi_abs.regs.CH0STAT with <|EOT := 1w; RXS := 1w|>;
RX0 := w2w (THE dataIN) |>;
RX_SHIFT_REG := THE dataIN;
xfer := spi_abs.xfer with state := abs_xfer_data_ready |>,
SOME spi_abs.TX_SHIFT_REG)
else (spi_abs, NONE)`

val _ = export_theory();
