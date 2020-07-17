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
 * In other words, load TX0's data to the SPI shift register.
 * xfer_trans_data_op : spi_state -> spi_state
 *)
val xfer_trans_data_op_def = Define `
xfer_trans_data_op (spi:spi_state) =
spi with <| (* TX0 -> shift register *)
SHIFT_REG := spi.regs.TX0;
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with <| EOT := 0w; TXS := 1w |>;
xfer := spi.xfer with state := xfer_exchange_data |>`

(* SPI controller's operation to perform the data exchange with the slave.
 * Basiclly, Master shift reg <-> Slave shift reg, slave receives the output data. Master receives slave's input data.
 *)
val xfer_exchange_data_op_def = Define `
xfer_exchange_data_op (env:environment) (spi:spi_state) =
spi with <|(* slave shift reg -> master shift reg *)
SHIFT_REG := env.SHIFT_REG; (* receive a word *)
regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with EOT := 1w;
xfer := spi.xfer with state := xfer_update_RX0 |>`
(* env is also updated: env.SHIFT_REG := (old) spi.SHIFT_REG, send a word *)

(* SPI controller handles the received word from shift register to RX0 
 * xfer_update_RX0_op: spi_state -> spi_state
 *)
val xfer_update_RX0_op_def = Define `
xfer_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* shift register -> RX0 *)
<|RX0 := spi.SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
xfer := spi.xfer with state := xfer_data_ready |>`

(* SPI controller operation after the driver issues a read(RX0) request
 * xfer_check_op: spi_state -> spi_state
 *)
val xfer_check_op_def = Define `
xfer_check_op (spi:spi_state) =
if (CHECK_TXS_BIT spi) /\ ~(CHECK_RXS_BIT spi) /\ (CHECK_EOT_BIT spi) then
spi with xfer := spi.xfer with state := xfer_ready_for_trans
else spi with err := T`

(* This function indicates SPI controller's  operations for xfer mode(full-duplex).
 * spi_xfer_operations: environment -> spi_state -> spi_state 
 *)
val spi_xfer_operations_def = Define `
spi_xfer_operations (env:environment) (spi:spi_state) =
case spi.xfer.state of
  | xfer_idle => spi with err := T
  | xfer_conf_ready => spi with err := T
  | xfer_channel_enabled => xfer_channel_enabled_op spi
  | xfer_ready_for_trans => spi with err := T
  | xfer_trans_data => xfer_trans_data_op spi
  | xfer_exchange_data => xfer_exchange_data_op env spi
  | xfer_update_RX0 => xfer_update_RX0_op spi
  | xfer_data_ready => spi with err := T
  | xfer_check => xfer_check_op spi
  | xfer_channel_disabled => spi with err := T`

val _ = export_theory();
