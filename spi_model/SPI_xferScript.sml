open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_xfer";

(* SPI controller operations when channel 0 is enabled for xfer.
 * xfer_channel_enabled_op:spi_state -> spi_state
 *)
val xfer_channel_enabled_op_def = Define `
xfer_channel_enabled_op (spi:spi_state) = 
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <|RXS := 0w; TXS := 1w|>;
xfer := spi.xfer with state := xfer_ready_for_trans |>`

(* SPI controller's operation to start the data exchange with the slave 
 * after the driver issues write(TX0, data) request.
 * TX0 -> SPI TX_SHIFT_REG
 * xfer_trans_data_op : spi_state -> spi_state
 *)
val xfer_trans_data_op_def = Define `
xfer_trans_data_op (spi:spi_state) =
spi with <| (* TX0 -> TX_shift_register *)
TX_SHIFT_REG := w2w spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| EOT := 0w; TXS := 1w |>;
xfer := spi.xfer with state := xfer_exchange_data |>`

(* SPI controller's operation to perform the data exchange with another SPI device.
 * Basiclly, Master TX_shift_reg -> Slave RX_shift_reg and Slave TX_shift_reg -> Master RX_Shift_reg.
 * xfer_exchange_data_op_def: spi_state -> word8 option-> spi_state * word8 option
 *)
val xfer_exchange_data_op_def = Define `
xfer_exchange_data_op (spi:spi_state) (dataIN:word8 option) =
if (spi.xfer.state = xfer_exchange_data) /\ (spi.regs.CH0STAT.TXS = 1w) /\
(spi.regs.CH0STAT.RXS = 0w) /\ (dataIN <> NONE) then
(spi with <|regs := spi.regs 
with CH0STAT := spi.regs.CH0STAT with EOT := 1w;
RX_SHIFT_REG := (THE dataIN);
xfer := spi.xfer with state := xfer_update_RX0 |>,
SOME spi.TX_SHIFT_REG)
else (spi, NONE)`

(* SPI controller handles the received word from shift register to RX0 
 * xfer_update_RX0_op: spi_state -> spi_state
 *)
val xfer_update_RX0_op_def = Define `
xfer_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* shift register -> RX0 *)
<|RX0 := w2w spi.RX_SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
xfer := spi.xfer with state := xfer_data_ready |>`

(* SPI controller operation after the driver issues a read(RX0) request
 * xfer_check_op: spi_state -> spi_state
 *)
val xfer_check_op_def = Define `
xfer_check_op (spi:spi_state) =
if (CHECK_TXS_BIT spi) /\ ~(CHECK_RXS_BIT spi) /\ (CHECK_EOT_BIT spi) then
spi with xfer := spi.xfer with state := xfer_ready_for_trans
else spi`

(* This function indicates SPI controller internal operations for xfer mode(full-duplex).
 * spi_xfer_operations: spi_state -> spi_state 
 *)
val spi_xfer_operations_def = Define `
spi_xfer_operations (spi:spi_state) =
case spi.xfer.state of
  | xfer_idle => spi with err := T
  | xfer_conf_ready => spi with err := T
  | xfer_channel_enabled => xfer_channel_enabled_op spi
  | xfer_ready_for_trans => spi with err := T
  | xfer_trans_data => xfer_trans_data_op spi
  | xfer_exchange_data => spi with err := T
  | xfer_update_RX0 => xfer_update_RX0_op spi
  | xfer_data_ready => spi with err := T
  | xfer_check => xfer_check_op spi
  | xfer_channel_disabled => spi with err := T`

val _ = export_theory();
