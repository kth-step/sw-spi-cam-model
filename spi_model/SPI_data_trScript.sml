open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_data_tr";

(* SPI data transition for TX label *)
(* This function returns a new spi state and the data to be transmitted.
 * tx_trans_done_op: spi_state -> spi_state * word8 option
 *)
val tx_trans_done_op_def = Define `
tx_trans_done_op (spi:spi_state) = 
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
(* An SPI word is transferred from the TX shift register to the slave *)
with EOT := 1w;
state := tx_ready_for_trans |>,
SOME spi.TX_SHIFT_REG)`

(* return specific datatype from above function *)
val tx_trans_done_op_state_def = Define `
tx_trans_done_op_state (spi:spi_state) =
let (spi', v_option) = tx_trans_done_op spi in spi'`

val tx_trans_done_op_value_def = Define `
tx_trans_done_op_value (spi:spi_state) =
let (spi', v_option) = tx_trans_done_op spi in v_option`

(* SPI data transition for RX label *)
(* rx_receive_data_op: spi_state -> word8 option -> spi_state *)
val rx_receive_data_op_def = Define `
rx_receive_data_op (spi:spi_state) (data:word8 option) =
if (data <> NONE) then 
spi with <| RX_SHIFT_REG := THE data; (* a word is received over the wire *)
state := rx_update_RX0 |>
else spi with err := T`

(* SPI data transition for XFER label *)
(* Master TX_shift_reg -> Slave RX_shift_reg and Slave TX_shift_reg -> Master RX_Shift_reg.
 * xfer_exchange_data_op_def: spi_state -> word8 option-> spi_state * word8 option
 *)
val xfer_exchange_data_op_def = Define `
xfer_exchange_data_op (spi:spi_state) (dataIN:word8 option) =
if (dataIN <> NONE) then
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT with EOT := 1w;
RX_SHIFT_REG := (THE dataIN);
state := xfer_update_RX0 |>,
SOME spi.TX_SHIFT_REG)
else (spi with err := T, NONE)`

(* return specific datatype from above function *)
val xfer_exchange_data_op_state_def = Define `
xfer_exchange_data_op_state (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in spi'`

val xfer_exchange_data_op_value_def = Define `
xfer_exchange_data_op_value (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in v_option`

val _ = export_theory();
