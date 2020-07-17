open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_rx";

(* SPI controller operation for rx when channel 0 is enabled.
 * rx_channel_enabled_op : spi_state -> spi_state
 *)
val rx_channel_enabled_op_def = Define `
rx_channel_enabled_op (spi:spi_state) =
spi with <| regs := spi.regs with CH0STAT := spi.regs.CH0STAT
with RXS := 0w (* RXS is cleared when enable the channel *);
rx := spi.rx with state := rx_receive_data |>`

(* SPI controller operation that indicates the hardware receives data(a word)
 * from the slave over the wire, Slave shift reg -> Master SPI shift reg.
 * rx_receive_data_op: environment -> spi_state -> spi_state
 *)
val rx_receive_data_op_def = Define `
rx_receive_data_op (env:environment) (spi:spi_state) =
spi with <| SHIFT_REG := env.SHIFT_REG; (* a word is received over the wire *)
rx := spi.rx with state := rx_update_RX0 |>`

(* SPI controller operation when the received word is transferred
 * from the shift register to the RX0 register, shift reg -> RX0.
 * rx_update_RX0_op: spi_state -> spi_state
 *)
val rx_update_RX0_op_def = Define `
rx_update_RX0_op (spi:spi_state) =
spi with <| regs := spi.regs with
(* a received word is transferred from shift register to RX0 *)
<|RX0 := spi.SHIFT_REG;
CH0STAT := spi.regs.CH0STAT with RXS := 1w |>;
rx := spi.rx with state := rx_data_ready |>`

(* SPI controller operation after the driver issues a read (RX0) request.
 * rx_receive_check_op: spi_state -> spi_state
 *)
val rx_receive_check_op_def = Define `
rx_receive_check_op (spi:spi_state) =
if ~(CHECK_RXS_BIT spi) then
spi with rx := spi.rx with state := rx_receive_data
else spi with err := T`

(* This function indicates SPI controller's operations for rx automaton.
 * spi_rx_operations: spi_state -> spi_state
 *)
val spi_rx_operations_def = Define `
spi_rx_operations (env:environment) (spi: spi_state) =
case spi.rx.state of
| rx_idle => spi with err := T
| rx_conf_ready => spi with err := T
| rx_channel_enabled => rx_channel_enabled_op spi
| rx_receive_data => rx_receive_data_op env spi
| rx_update_RX0 => rx_update_RX0_op spi 
| rx_data_ready => spi with err := T
| rx_receive_check => rx_receive_check_op spi
| rx_channel_disabled => spi with err := T`


val _ = export_theory ();
