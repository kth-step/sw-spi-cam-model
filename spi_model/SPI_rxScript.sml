open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_rx";

(* SPI controller operation for rx mode when channel 0 is enabled.
 * rx_channel_enabled_op : spi_state -> spi_state
 *)
val rx_channel_enabled_op_def = Define `
rx_channel_enabled_op (spi:spi_state) =
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with RXS := 0w (* RXS is cleared when enable the channel *);
rx := spi.rx with state := rx_receive_data |>`

(* SPI controller operation indicates the hardware receives data(a word) from another SPI device.
 * rx_receive_data_op: spi_state -> word8 option -> spi_state
 *)
val rx_receive_data_op_def = Define `
rx_receive_data_op (spi:spi_state) (data: word8 option) =
if (spi.rx.state = rx_receive_data) /\ (data <> NONE) then 
spi with <| RX_SHIFT_REG := THE data; (* a word is received over the wire *)
rx := spi.rx with state := rx_update_RX0 |>
else spi`

(* SPI controller operation when the received word is transferred
 * from the shift register to its RX0 register, RX_SHIFT_REG -> RX0.
 * rx_update_RX0_op: spi_state -> spi_state
 *)
val rx_update_RX0_op_def = Define `
rx_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* a received word is transferred from shift register to RX0 *)
<|RX0 := w2w spi.RX_SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
rx := spi.rx with state := rx_data_ready |>`

(* SPI controller operation after the CPU/driver issues a read (RX0) request.
 * rx_receive_check_op: spi_state -> spi_state
 *)
val rx_receive_check_op_def = Define `
rx_receive_check_op (spi:spi_state) =
spi with rx := spi.rx with state := rx_receive_data`

(* This function indicates SPI controller's operations for rx automaton.
 * spi_rx_operations: spi_state -> spi_state
 *)
val spi_rx_operations_def = Define `
spi_rx_operations (spi:spi_state) =
case spi.rx.state of
| rx_idle => spi with err := T
| rx_conf_ready => spi with err := T
| rx_channel_enabled => rx_channel_enabled_op spi
| rx_receive_data => spi with err := T
| rx_update_RX0 => rx_update_RX0_op spi 
| rx_data_ready => spi with err := T
| rx_receive_check => rx_receive_check_op spi
| rx_channel_disabled => spi with err := T`


val _ = export_theory ();
