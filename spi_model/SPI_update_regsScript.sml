open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "SPI_update_regs";

(* write a value(1) to spi.regs.SYSCONFIG.SOFTRESET, start to reset SPI hardware.
 * write_SOFTRESET: word32 -> spi_state -> spi_state
 *)
val write_SOFTRESET_def = Define `
write_SOFTRESET (value:word32) (spi:spi_state) =
let v = (1 >< 1) value :word1 in
if (spi.state = init_start) /\ (v = 1w) (* v = 1w, start a module reset *) then
spi with <| regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; (* automatically reset by hardware *)
SYSSTATUS := 0w |>;
state := init_reset;
init := spi.init with 
<| sysconfig_mode_done := F; modulctrl_bus_done := F; 
ch0conf_wordlen_done := F; ch0conf_mode_done := F;
ch0conf_speed_done := F |> |>
else if (spi.state = spi_ready) /\ (v = 1w) then
spi with <| regs := spi.regs with 
<|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; SYSSTATUS := 0w |>;
state := init_reset;
init := spi.init with 
<| sysconfig_mode_done := F; modulctrl_bus_done:= F; 
   ch0conf_wordlen_done := F; ch0conf_mode_done := F;
   ch0conf_speed_done := F |> |>
else spi with err := T (* SPI is not ready to reset *)`

(* write a value to spi.regs.SYSCONFIG, set some bits of SYSCONFIG 
 * write_SYSCONFIG_def: word32 -> spi_state -> spi_state
 *)
val write_SYSCONFIG_def = Define `
write_SYSCONFIG (value:word32) (spi:spi_state) =
let v1 = (0 >< 0) value:word1 and
    v2 = (4 >< 3) value: word2 in
if (spi.state = init_setregs) /\ (v1 = 1w) /\ (v2 = 2w) then
spi with <| regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w |>;
init := spi.init with sysconfig_mode_done := T;
state := 
if (spi.init.modulctrl_bus_done /\ spi.init.ch0conf_wordlen_done 
/\ spi.init.ch0conf_mode_done /\ spi.init.ch0conf_speed_done) 
then spi_ready else init_setregs |> 
else spi with err := T`

(* When PA = SPI0_SYSCONFIG, call functions according to the value.
 * write_SYSCONFIG_comb: word32 -> spi_state -> spi_state *)
val write_SYSCONFIG_comb_def = Define `
write_SYSCONFIG_comb (value:word32) (spi:spi_state) =
if ((1 >< 1) value:word1 = 1w)
then (write_SOFTRESET value spi) 
else if ((0 >< 0) value:word1 = 1w) /\ ((4 >< 3) value:word2 = 2w)
then (write_SYSCONFIG value spi) 
else spi with err := T`

(* write a value to spi.regs.MODULCTRL, set to a single-channel master mode.
 * write_MODULCTRL: word32 -> spi_state -> spi_state
 *)
val write_MODULCTRL_def = Define `
write_MODULCTRL (value:word32) (spi:spi_state) =
let v1 = (0 >< 0) value: word1 and
    v2 = (2 >< 2) value: word1 and
    v3 = (3 >< 3) value: word1 in
if (spi.state = init_setregs) /\ (v1 = 1w) /\ (v3 = 0w) then
spi with <| regs := spi.regs with MODULCTRL := spi.regs.MODULCTRL with
<| SYSTEM_TEST := v3; MS := v2; SINGLE := v1 |>;
init := spi.init with modulctrl_bus_done := T;
state := 
if (spi.init.sysconfig_mode_done /\ spi.init.ch0conf_wordlen_done 
/\ spi.init.ch0conf_mode_done /\ spi.init.ch0conf_speed_done) 
then spi_ready else init_setregs |> 
else spi with err := T`

(* write a value to spi.regs.CH0CONF with WL bit 
 * write_CH0CONF_WL: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_WL_def = Define `
write_CH0CONF_WL (value:word32) (spi:spi_state) =
let v = (11 >< 7) value:word5 in
if (spi.state = init_setregs) /\ (v >+ 2w) (* Bit WL should be bigger than 2w *) then 
spi with <| regs := spi.regs with 
CH0CONF := spi.regs.CH0CONF with WL := v;
init := spi.init with ch0conf_wordlen_done := T;
state := 
if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
/\ spi.init.ch0conf_mode_done /\ spi.init.ch0conf_speed_done) 
then spi_ready else init_setregs |> 
else spi with err := T`

(* write a value to spi.regs.CH0CONF to set common bits, 
 * including IS, DPE1, DPE0, TRM, EPOL, POL, PHA.
 * write_CH0CONF: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_def = Define `
write_CH0CONF (value:word32) (spi:spi_state) =
let v1 = (18 >< 18) value:word1 and
    v2 = (17 >< 17) value:word1 and
    v3 = (16 >< 16) value:word1 and
    v4 = (13 >< 12) value:word2 and
    v5 = (6 >< 6) value:word1 and
    v6 = (1 >< 1) value:word1 and
    v7 = (0 >< 0) value:word1 in
if (spi.state = init_setregs) /\ (v4 <> 3w) then 
spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF with 
<| IS := v1; DPE1 := v2; DPE0 := v3;
TRM := v4; EPOL := v5; POL := v6; PHA := v7 |>;
init := spi.init with ch0conf_mode_done := T;
state := 
if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
/\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_speed_done) 
then spi_ready else init_setregs |>
else spi with err := T`

(* write a value to spi.regs.CH0CONF to set speed 
 * write_CH0CONF_speed: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_speed_def = Define `
write_CH0CONF_speed (value:word32) (spi:spi_state) =
let v = (5 >< 2) value:word4 in
if spi.state = init_setregs then
spi with <|regs := spi.regs with
CH0CONF := spi.regs.CH0CONF with CLKD := v;
init := spi.init with ch0conf_speed_done := T;
state := 
if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
/\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done)
then spi_ready else init_setregs |>
else spi with err := T`

(* enable or disable the SPI channel 0 for tx, rx and xfer automatons.
 * write_CH0CTRL: word32 -> spi_state -> spi_state
 *)
val write_CH0CTRL_def = Define `
write_CH0CTRL (value:word32) (spi:spi_state) =
let v = (0 >< 0) value:word1 in
if (spi.state = tx_conf_ready) /\ (v = 1w) 
then spi with <| regs := spi.regs with 
     <| CH0CTRL := 1w; CH0STAT := spi.regs.CH0STAT with TXS := 0w |>;
     state := tx_channel_enabled |>
else if (spi.state = tx_ready_for_trans) /\ (v = 0w)
then spi with <| regs := spi.regs with CH0CTRL := 0w;
     state := tx_channel_disabled |>
else if (spi.state = rx_conf_ready) /\ (v = 1w)
then spi with <|regs := spi.regs with 
     <| CH0CTRL := 1w; CH0STAT := spi.regs.CH0STAT with RXS := 0w |>;
     state := rx_channel_enabled |>
else if (spi.state = rx_data_ready) /\ (v = 0w)
then spi with <|regs := spi.regs with CH0CTRL := 0w;
     state := rx_channel_disabled |>
else if (spi.state = xfer_conf_ready) /\ (v = 1w)
then spi with <|regs := spi.regs with 
     <| CH0CTRL := 1w; CH0STAT := spi.regs.CH0STAT with <| TXS := 0w; RXS := 0w |> |>;
     state := xfer_channel_enabled |>
else if (spi.state = xfer_ready_for_trans) /\ (v = 0w)
then spi with <|regs := spi.regs with CH0CTRL := 0w;
     state := xfer_channel_disabled |>
else spi with err := T`


(* write a value to spi.regs.CH0CONF to start and finish the tx automaton, vaild when TRM = 2.
 * write_CH0CONF_tx: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_tx_def = Define `
write_CH0CONF_tx (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
if (spi.state = spi_ready) /\ (v1 = 2w) /\ (v2 = 1w) then 
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF
with <|TRM := 2w; FORCE := 1w |>;
state := tx_conf_ready |> 
else if (spi.state = tx_channel_disabled) /\ (v2 = 0w) then
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF with FORCE := 0w;
state := spi_ready |> 
else spi with err := T`

(* write the spi.regs.CH0CONF to start and finish the rx process, vaild when TRM = 1. 
 * write_CH0CONF_rx: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_rx_def = Define `
write_CH0CONF_rx (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
if (spi.state = spi_ready) /\ (v1 = 1w) /\ (v2 = 1w) then
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF
with <|TRM := 1w; FORCE := 1w|>;
state := rx_conf_ready |>
else if (spi.state = rx_channel_disabled) /\ (v2 = 0w) then
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF with FORCE := 0w;
state := spi_ready |> 
else spi with err := T`

(* write the spi.regs.CH0CONF to start and finish the xfer process, vaild when TRM = 0 
 * write_CH0CONF_xfer: word32 -> spi_state -> spi_state
 *)
val write_CH0CONF_xfer_def = Define `
write_CH0CONF_xfer (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
if (spi.state = spi_ready) /\ (v1 = 0w) /\ (v2 = 1w) then
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF
with  <| TRM := 0w; FORCE := 1w |>;
state := xfer_conf_ready |> 
else if (spi.state = xfer_channel_disabled) /\ (v2 = 0w) then
spi with <| regs := spi.regs with CH0CONF := spi.regs.CH0CONF  with FORCE := 0w;
state := spi_ready |> 
else spi with err := T`

(* write_CH0CONF_comb: word32 -> spi_state -> spi_state *)
val write_CH0CONF_comb_def = Define `
write_CH0CONF_comb (value:word32) (spi:spi_state) =
if ((11 >< 7) value:word5 <> 0w) 
then (write_CH0CONF_WL value spi) 
else if ((17 >< 16) value:word2 <> 0w) 
then (write_CH0CONF value spi) 
else if ((5 >< 2) value:word4 <> 0w) 
then (write_CH0CONF_speed value spi) 
else if ((13 >< 12) value:word2 = 2w) \/ (value = 0w /\ spi.state = tx_channel_disabled)
then (write_CH0CONF_tx value spi)
else if ((13 >< 12) value:word2 = 1w) \/ (value = 0w /\ spi.state = rx_channel_disabled)
then (write_CH0CONF_rx value spi) 
else if ((13 >< 12) value:word2 = 0w) \/ (value = 0w /\ spi.state = xfer_channel_disabled) 
then (write_CH0CONF_xfer value spi)
else spi with err := T`

(* clear the TXS bit when write a byte to TX0 register.
 * write_TX0: word32 -> spi_state -> spi_state
 *)
val write_TX0_def = Define `
write_TX0 (value:word32) (spi:spi_state) =
if (CHECK_TXS_BIT spi) /\ (spi.state = tx_ready_for_trans) then
spi with <| regs := spi.regs with <| CH0STAT := spi.regs.CH0STAT with TXS := 0w;
TX0 := ((7 >< 0) value:word32) |>;
state := tx_trans_data |>
else if (CHECK_TXS_BIT spi) /\ (spi.state = tx_trans_done) then
spi with <| regs := spi.regs with <| CH0STAT := spi.regs.CH0STAT with TXS := 0w;
TX0 := ((7 >< 0) value:word32) |>;
state := tx_trans_next |>
else if (CHECK_TXS_BIT spi) /\ (spi.state = xfer_ready_for_trans) then
spi with <| regs := spi.regs with <| CH0STAT := spi.regs.CH0STAT with TXS := 0w;
TX0 := ((7 >< 0) value:word32) |>;
state := xfer_trans_data |>
else spi with err := T`

(* write_SPI_regs_def: word32 -> word32 -> spi_state -> spi_state *)
val write_SPI_regs_def = Define `
write_SPI_regs (pa:word32) (value:word32) (spi:spi_state) =
if ~(pa IN SPI0_PA_RANGE) then spi
else if (pa = SPI0_SYSCONFIG) then (write_SYSCONFIG_comb value spi)
else if (pa = SPI0_MODULCTRL) then (write_MODULCTRL value spi)
else if (pa = SPI0_CH0CONF) then (write_CH0CONF_comb value spi)
else if (pa = SPI0_CH0CTRL) then (write_CH0CTRL value spi)
else if (pa = SPI0_TX0) then (write_TX0 value spi)
(* SYSSTATUS, RX0, CH0STAT are read-only 
else if (pa = SPI0_SYSSTATUS) then spi
else if (pa = SPI0_RX0) then spi
else if (pa = SPI0_CH0STAT) then spi
*)
(* write to non-modeled or read-only address in SPI, no changes *)
else spi`

val _ = export_theory();
