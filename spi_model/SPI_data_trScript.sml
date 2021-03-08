open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_data_tr";

(* SPI data transition for TX label *)
(* tx_trans_done_op: returns a new spi state and the data to be transmitted. *)
val tx_trans_done_op_def = Define `
tx_trans_done_op (spi:spi_state) = 
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
(* An SPI word is transferred from the TX shift register to the slave *)
with EOT := 1w;
state := tx_ready_for_trans |>,
SOME spi.TX_SHIFT_REG)`

(* tx_trans_next_op: similiar with tx_trans_done_op. *)
val tx_trans_next_op_def = Define `
tx_trans_next_op (spi:spi_state) =
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with EOT := 1w;
state := tx_trans_update |>,
SOME spi.TX_SHIFT_REG)`

(* tx_TX_op: combine previous two functions *)
val tx_TX_op_def = Define `
tx_TX_op (spi:spi_state) =
if spi.state = tx_trans_done then (tx_trans_done_op spi)
else if spi.state = tx_trans_next then  (tx_trans_next_op spi)
else (spi with err := T, NONE)`

(*  tx_TX_op_state, tx_trans_done_op_value: return specific datatype from above function *)
val tx_TX_op_state_def = Define `
tx_TX_op_state (spi:spi_state) =
let (spi', v_option) = tx_TX_op spi in spi'`

val tx_trans_done_op_value_def = Define `
tx_TX_op_value (spi:spi_state) =
let (spi', v_option) = tx_TX_op spi in v_option`

(* SPI data transition for RX label *)
(* rx_receive_data_op: receive one byte in the rx mode *)
val rx_receive_data_op_def = Define `
rx_receive_data_op (spi:spi_state) (data:word8 option) =
if (data <> NONE) then 
spi with <| RX_SHIFT_REG := THE data;
state := rx_update_RX0 |>
else spi with err := T`

(* SPI data transition for XFER label *)
(* xfer_exchange_data_op: one SPI device (the master) exchange the data with another device (the slave). *)
val xfer_exchange_data_op_def = Define `
xfer_exchange_data_op (spi:spi_state) (dataIN:word8 option) =
if (dataIN <> NONE) then
(spi with <|regs := spi.regs with CH0STAT := spi.regs.CH0STAT with EOT := 1w;
RX_SHIFT_REG := (THE dataIN);
state := xfer_update_RX0 |>,
SOME spi.TX_SHIFT_REG)
else (spi with err := T, NONE)`

(* xfer_exchange_data_op_state, xfer_exchange_data_op_value: return specific datatype from above function.*)
val xfer_exchange_data_op_state_def = Define `
xfer_exchange_data_op_state (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in spi'`

val xfer_exchange_data_op_value_def = Define `
xfer_exchange_data_op_value (spi:spi_state) (dataIN: word8 option) =
let (spi', v_option) = xfer_exchange_data_op spi dataIN in v_option`

val _ = export_theory();
