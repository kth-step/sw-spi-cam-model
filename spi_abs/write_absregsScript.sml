open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open spi_absstateTheory board_memTheory;

(* If the driver issues a write request, spi_abs updates its state.
 * In the abs model, the update function does not only update registers, 
 * but also perform some internal operations (tau transiton).
 *)
val _ = new_theory "write_absregs";

(* write_abs_SOFTRESET: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_SOFTRESET_def = Define `
write_abs_SOFTRESET (value:word32) (spi_abs:spi_abs_state) =
let v = (1 >< 1) value :word1 in 
case spi_abs.init.state of
  | abs_init_start => if v = 0w then spi_abs
    else spi_abs with <|regs := spi_abs.regs with
    <|SYSCONFIG := spi_abs.regs.SYSCONFIG with SOFTRESET := 0w;
      SYSSTATUS := 1w (* internal *)|>;
    init := spi_abs.init with 
    <|state := abs_init_setregs; 
    sysconfig_mode_done := F; 
    modulctrl_bus_done := F; 
    ch0conf_wordlen_done := F; 
    ch0conf_mode_done := F;
    ch0conf_speed_done := F |> |>
  | abs_init_setregs => spi_abs with err := T
  | abs_init_done => 
    if ((v = 1w) /\ (spi_abs.tx.state <> abs_tx_idle \/ spi_abs.rx.state 
    <> abs_rx_idle \/ spi_abs.xfer.state <> abs_xfer_idle)) then
    spi_abs with err := T
    else if v = 1w then
    spi_abs with <|regs := spi_abs.regs with
    <|SYSCONFIG := spi_abs.regs.SYSCONFIG with SOFTRESET := 0w;
      SYSSTATUS := 1w (* internal *)|>;
    init := spi_abs.init with 
    <|state := abs_init_setregs; 
    sysconfig_mode_done := F; 
    modulctrl_bus_done := F; 
    ch0conf_wordlen_done := F; 
    ch0conf_mode_done := F;
    ch0conf_speed_done := F |> |>
    else spi_abs`

(* write_abs_SYSCONFIG_def: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_SYSCONFIG_def = Define `
write_abs_SYSCONFIG (value:word32) (spi_abs:spi_abs_state) =
let v1 = (0 >< 0) value:word1 and
    v2 = (4 >< 3) value: word2 in
case spi_abs.init.state of
  | abs_init_start => spi_abs with err := T
  | abs_init_setregs => if (v1 = 1w) /\ (v2 = 2w) then
    spi_abs with <| regs := spi_abs.regs with 
    SYSCONFIG := spi_abs.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
    init := spi_abs.init with 
    <|sysconfig_mode_done := T;
      state := 
      if (spi_abs.init.modulctrl_bus_done 
      /\ spi_abs.init.ch0conf_wordlen_done /\ spi_abs.init.ch0conf_mode_done 
      /\ spi_abs.init.ch0conf_speed_done) then abs_init_done else abs_init_setregs|> |> 
    else spi_abs with err := T
  | abs_init_done => spi_abs with err := T`

(* write_abs_SYSCONFIG_comb: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_SYSCONFIG_comb_def = Define `
write_abs_SYSCONFIG_comb (value:word32) (spi_abs:spi_abs_state) =
let spi_abs = if ((1 >< 1) value:word1 = 1w) 
then (write_abs_SOFTRESET value spi_abs) else spi_abs in
if ((0 >< 0) value:word1 = 1w) 
then (write_abs_SYSCONFIG value spi_abs) else spi_abs`

(* write_abs_MODULCTRL: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_MODULCTRL_def = Define `
write_abs_MODULCTRL (value:word32) (spi_abs:spi_abs_state) =
let v1 = (0 >< 0) value: word1 and
    v2 = (2 >< 2) value: word1 and
    v3 = (3 >< 3) value: word1 in
case spi_abs.init.state of
  | abs_init_start => spi_abs with err := T
  | abs_init_setregs => if ((v1 = 1w) /\ (v3 = 0w)) then
    spi_abs with <| regs := spi_abs.regs with MODULCTRL := spi_abs.regs.MODULCTRL with
    <|SYSTEM_TEST := v3; MS := v2; SINGLE := v1|>;
    init := spi_abs.init with <|modulctrl_bus_done := T;
    state := 
    if (spi_abs.init.sysconfig_mode_done
    /\ spi_abs.init.ch0conf_wordlen_done /\ spi_abs.init.ch0conf_mode_done 
    /\ spi_abs.init.ch0conf_speed_done) then abs_init_done else abs_init_setregs|> |> 
    else spi_abs with err := T
  | abs_init_done => spi_abs with err := T`

(* write_abs_CH0CONF_WL: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_WL_def = Define `
write_abs_CH0CONF_WL (value:word32) (spi_abs:spi_abs_state) =
let v = (11 >< 7) value:word5 in
case spi_abs.init.state of
  | abs_init_start => spi_abs with err := T
  | abs_init_setregs => if v >+ 2w then 
    spi_abs with <|regs := spi_abs.regs with 
    CH0CONF := spi_abs.regs.CH0CONF with WL := v;
    init := spi_abs.init with <|ch0conf_wordlen_done := T;
    state := 
    if (spi_abs.init.sysconfig_mode_done /\ spi_abs.init.modulctrl_bus_done 
    /\ spi_abs.init.ch0conf_mode_done 
    /\ spi_abs.init.ch0conf_speed_done) then abs_init_done else abs_init_setregs|> |> 
    else spi_abs with err := T
  | abs_init_done => spi_abs with err := T`

(* write_abs_CH0CONF:word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_def = Define `
write_abs_CH0CONF (value:word32) (spi_abs:spi_abs_state) =
let v1 = (18 >< 18) value:word1 and
    v2 = (17 >< 17) value:word1 and
    v3 = (16 >< 16) value:word1 and
    v4 = (13 >< 12) value:word2 and
    v5 = (6 >< 6) value:word1 and
    v6 = (1 >< 1) value:word1 and
    v7 = (0 >< 0) value:word1 in
case spi_abs.init.state of
  | abs_init_start => spi_abs with err := T
  | abs_init_setregs => if v4 = 3w then spi_abs with err := T
    else spi_abs with <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF with 
    <|IS := v1; DPE1 := v2; DPE0 := v3;
      TRM := v4; EPOL := v5; POL := v6; PHA := v7|>;
    init := spi_abs.init with <|ch0conf_mode_done := T;
    state := 
    if (spi_abs.init.sysconfig_mode_done /\ spi_abs.init.modulctrl_bus_done 
     /\ spi_abs.init.ch0conf_wordlen_done /\ spi_abs.init.ch0conf_speed_done) 
    then abs_init_done else abs_init_setregs |> |>
  | abs_init_done => spi_abs with err := T`

(* write_abs_CH0CONF_speed: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_speed_def = Define `
write_abs_CH0CONF_speed (value:word32) (spi_abs:spi_abs_state) =
let v = (5 >< 2) value:word4 in
case spi_abs.init.state of
  | abs_init_start => spi_abs with err := T
  | abs_init_setregs => 
     spi_abs with <|regs := spi_abs.regs with
     CH0CONF := spi_abs.regs.CH0CONF with CLKD := v;
     init := spi_abs.init with <|ch0conf_speed_done := T;
     state := 
     if (spi_abs.init.sysconfig_mode_done /\ spi_abs.init.modulctrl_bus_done 
     /\ spi_abs.init.ch0conf_wordlen_done /\ spi_abs.init.ch0conf_mode_done)
     then abs_init_done else abs_init_setregs |> |>
  | abs_init_done => spi_abs with err := T`

(* write_abs_CH0CONF_tx: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_tx_def = Define `
write_abs_CH0CONF_tx (value:word32) (spi_abs:spi_abs_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case spi_abs.tx.state of
  | abs_tx_idle =>
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.rx.state = abs_rx_idle)
    /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v1 = 2w) /\ (v2 = 1w) then
    spi_abs with <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF
    with <|TRM := 2w; FORCE := 1w |>;
    tx := spi_abs.tx with state := abs_tx_conf_ready |>
    else spi_abs with err := T   
  | abs_tx_conf_ready => spi_abs with err := T
  | abs_tx_ready_for_trans => spi_abs with err := T
  | abs_tx_trans_done => spi_abs with err := T
  | abs_tx_channel_disabled => 
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.rx.state = abs_rx_idle)
    /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v2 = 0w) then
    spi_abs with 
    <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF with FORCE := 0w;
    tx := spi_abs.tx with state := abs_tx_idle |> 
    else spi_abs with err := T`

(* write_abs_CH0CONF_rx: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_rx_def = Define `
write_abs_CH0CONF_rx (value:word32) (spi_abs:spi_abs_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case spi_abs.rx.state of
  | abs_rx_idle => 
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
    /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v1 = 1w) /\ (v2 = 1w) then
    spi_abs with <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF
    with <|TRM := 1w; FORCE := 1w|>;
    rx := spi_abs.rx with state := abs_rx_conf_ready |>
    else spi_abs with err := T 
  | abs_rx_conf_ready => spi_abs with err := T
  | abs_rx_receive_data => spi_abs with err := T
  | abs_rx_data_ready => spi_abs with err := T
  | abs_rx_channel_disabled =>
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
    /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v2 = 0w) then
    spi_abs with 
    <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF with FORCE := 0w;
    rx := spi_abs.rx with state := abs_rx_idle |> 
    else spi_abs with err := T`

(* write_abs_CH0CONF_xfer: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_xfer_def = Define `
write_abs_CH0CONF_xfer (value:word32) (spi_abs:spi_abs_state) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case spi_abs.xfer.state of
  | abs_xfer_idle => 
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
    /\ (spi_abs.rx.state = abs_rx_idle) /\ (v1 = 0w) /\ (v2 = 1w) then
    spi_abs with <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF
    with <|TRM := 0w; FORCE := 1w |>;
    xfer := spi_abs.xfer with state := abs_xfer_conf_ready |>
    else spi_abs with err := T    
  | abs_xfer_conf_ready => spi_abs with err := T
  | abs_xfer_ready_for_trans => spi_abs with err := T
  | abs_xfer_exchange_data => spi_abs with err := T
  | abs_xfer_data_ready => spi_abs with err := T
  | abs_xfer_channel_disabled => 
    if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle) 
    /\ (spi_abs.rx.state = abs_rx_idle) /\ (v2 = 0w) then
    spi_abs with 
    <|regs := spi_abs.regs with CH0CONF := spi_abs.regs.CH0CONF with FORCE := 0w;
    xfer := spi_abs.xfer with state := abs_xfer_idle |> 
    else spi_abs with err := T`

(* write_abs_CH0CONF_comb: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CONF_comb_def = Define `
write_abs_CH0CONF_comb (value:word32) (spi_abs:spi_abs_state) =
let spi_abs = if ((11 >< 7) value:word5 <> 0w) 
then (write_abs_CH0CONF_WL value spi_abs) else spi_abs in
let spi_abs = if ((17 >< 16) value:word2 <> 0w) 
then (write_abs_CH0CONF value spi_abs) else spi_abs in
let spi_abs = if (value = 0w \/ ((5 >< 2) value:word4 <> 0w)) 
then (write_abs_CH0CONF_speed value spi_abs) else spi_abs in
let spi_abs = if ((13 >< 12) value:word2 = 2w) \/ (value = 0w /\ spi_abs.tx.state = abs_tx_channel_disabled)
then (write_abs_CH0CONF_tx value spi_abs) else spi_abs in
let spi_abs = if ((13 >< 12) value:word2 = 1w) \/ (value = 0w /\ spi_abs.rx.state = abs_rx_channel_disabled)
then (write_abs_CH0CONF_rx value spi_abs) else spi_abs in
if (((13 >< 12) value:word2 = 0w) /\ ((20 >< 20) value:word1 = 1w)) 
\/ (value = 0w /\ spi_abs.xfer.state = abs_xfer_channel_disabled) then
(write_abs_CH0CONF_xfer value spi_abs) else spi_abs`

(* write_abs_CH0CTRL: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_CH0CTRL_def = Define `
write_abs_CH0CTRL (value:word32) (spi_abs:spi_abs_state) =
let v = (0 >< 0) value:word1 in
if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_conf_ready)
/\ (spi_abs.rx.state = abs_rx_idle) /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v = 1w)
then spi_abs with <|regs := spi_abs.regs with 
     <|CH0CTRL := 1w; CH0STAT := spi_abs.regs.CH0STAT with TXS := 1w |>;
     tx := spi_abs.tx with state := abs_tx_ready_for_trans |>
else if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_ready_for_trans)
/\ (spi_abs.rx.state = abs_rx_idle) /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v = 0w)
then spi_abs with <|regs := spi_abs.regs with CH0CTRL := 0w;
     tx := spi_abs.tx with state := abs_tx_channel_disabled |>
else if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
/\ (spi_abs.rx.state = abs_rx_conf_ready) /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v = 1w)
then spi_abs with <|regs := spi_abs.regs with
     <|CH0CTRL := 1w; CH0STAT := spi_abs.regs.CH0STAT with RXS := 0w |>;
     rx := spi_abs.rx with state := abs_rx_receive_data |>
else if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
/\ (spi_abs.rx.state = abs_rx_receive_data) /\ (spi_abs.xfer.state = abs_xfer_idle) /\ (v = 0w)
then spi_abs with <|regs := spi_abs.regs with CH0CTRL := 0w;
     rx := spi_abs.rx with state := abs_rx_channel_disabled |>
else if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
/\ (spi_abs.rx.state = abs_rx_idle) /\ (spi_abs.xfer.state = abs_xfer_conf_ready) /\ (v = 1w)
then spi_abs with <|regs := spi_abs.regs with
     <|CH0CTRL := 1w; CH0STAT := spi_abs.regs.CH0STAT with <|RXS := 0w; TXS :=1w |> |>;
     xfer := spi_abs.xfer with state := abs_xfer_ready_for_trans |>
else if (spi_abs.init.state = abs_init_done) /\ (spi_abs.tx.state = abs_tx_idle)
/\ (spi_abs.rx.state = abs_rx_idle) /\ (spi_abs.xfer.state = abs_xfer_ready_for_trans) /\ (v = 0w)
then spi_abs with <|regs := spi_abs.regs with CH0CTRL := 0w;
     xfer := spi_abs.xfer with state := abs_xfer_channel_disabled |>
else spi_abs with err := T`

(* write_abs_TX0: word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_TX0_def = Define `
write_abs_TX0 (value:word32) (spi_abs:spi_abs_state) =
let wl = (w2n spi_abs.regs.CH0CONF.WL) in
if (spi_abs.regs.CH0STAT.TXS = 1w) /\ (spi_abs.regs.CH0CONF.WL >+ 2w)
/\ (spi_abs.tx.state = abs_tx_ready_for_trans) then
spi_abs with <|regs := spi_abs.regs with 
<|CH0STAT := spi_abs.regs.CH0STAT with <|EOT := 0w; TXS := 1w |>;
TX0 := ((wl >< 0) value:word32) |>;
TX_SHIFT_REG := w2w ((wl >< 0) value:word32);
tx := spi_abs.tx with state := abs_tx_trans_done |>
else if (spi_abs.regs.CH0STAT.TXS = 1w) /\ (spi_abs.regs.CH0CONF.WL >+ 2w)
/\ (spi_abs.xfer.state = abs_xfer_ready_for_trans) then
spi_abs with <|regs := spi_abs.regs with
<|CH0STAT := spi_abs.regs.CH0STAT with <|EOT := 0w; TXS := 1w |>;
TX0 := ((wl >< 0) value:word32) |>;
TX_SHIFT_REG := w2w ((wl >< 0) value:word32);
xfer := spi_abs.xfer with state := abs_xfer_exchange_data |>
else spi_abs with err := T`

(* write_abs_spi_regs: word32 -> word32 -> spi_abs_state -> spi_abs_state *)
val write_abs_spi_regs_def = Define `
write_abs_spi_regs (pa:word32) (value:word32) (spi_abs:spi_abs_state) =
if spi_abs.err then spi_abs
else if ~(pa IN SPI0_PA_RANGE) then spi_abs
else if (pa = SPI0_SYSCONFIG) then (write_abs_SYSCONFIG_comb value spi_abs)
else if (pa = SPI0_MODULCTRL) then (write_abs_MODULCTRL value spi_abs)
else if (pa = SPI0_CH0CONF) then (write_abs_CH0CONF_comb value spi_abs)
else if (pa = SPI0_CH0CTRL) then (write_abs_CH0CTRL value spi_abs)
else if (pa = SPI0_TX0) then (write_abs_TX0 value spi_abs)
(* write to non-modeled or read-only addresses, no changes *)
else spi_abs`

val _ = export_theory();
