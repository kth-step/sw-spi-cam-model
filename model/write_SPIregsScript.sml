open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "write_SPIregs";

(* write a value(1) to spi.regs.SYSCONFIG.SOFTRESET, start the reset process *)
val write_SOFTRESET_def = Define `
write_SOFTRESET (value:word32) (spi:spi_state) =
let v = (1 >< 1) value :word1 in
case spi.init.state of
| init_start => if v = 0w then spi with err := T
  else spi with <|regs := spi.regs with SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 1w;
                  init := spi.init with 
                  <|state := init_reset; 
                    sysconfig_mode_done := F; 
                    modulctrl_bus_done := F; 
                    ch0conf_wordlen_done := F; 
                    ch0conf_mode_done := F;
                    ch0conf_speed_done := F |> |>
| init_reset => spi with err := T
| init_setregs => spi with err := T
| init_done => if ((v = 1w) /\ (spi.tx.state <> tx_idle \/ spi.rx.state <> rx_idle)) then spi with err:= T
else if v = 1w then 
spi with <|regs := spi.regs with SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 1w;
                  init := spi.init with 
                  <|state := init_reset; 
                    sysconfig_mode_done := F; 
                    modulctrl_bus_done:= F; 
                    ch0conf_wordlen_done := F; 
                    ch0conf_wordlen_done := F |> |>
else spi`

(* write a value to spi.regs.SYSCONFIG, set some bits of SYSCONFIG *)
val write_SYSCONFIG_mode_def = Define `
write_SYSCONFIG_mode (value:word32) (spi:spi_state) =
let v1 = (0 >< 0) value:word1 and
v2 = (4 >< 3) value: word2 in
case spi.init.state of
  | init_start => spi with err := T
  | init_reset => spi with err := T
  | init_setregs => if ((v1 = 1w) /\ (v2 = 2w)) then
    spi with <|regs := spi.regs with 
    SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
    init := spi.init with 
    <|sysconfig_mode_done := T;
      state := if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
      /\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done 
      /\ spi.init.ch0conf_speed_done) then init_done else init_setregs|> |> 
    else spi with err := T
  | init_done => spi with err := T`

(* write a value to spi.regs.MODULCTRL, set to a single-channel master mode *)
val write_MODULCTRL_def = Define `
write_MODULCTRL (value:word32) (spi:spi_state) =
let v1 = (0 >< 0) value: word1 and
v2 = (2 >< 2) value: word1 and
v3 = (3 >< 3) value: word1 in
case spi.init.state of
  | init_start => spi with err := T 
  | init_reset => spi with err := T
  | init_setregs => if ((v1 = 1w) /\ (v2 = 0w) /\ (v3 = 0w)) then
    spi with <|regs := spi.regs with
    MODULCTRL := spi.regs.MODULCTRL with
    <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
      init := spi.init with <| modulctrl_bus_done := T;
      state := if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
      /\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done 
      /\ spi.init.ch0conf_speed_done) then init_done else init_setregs|> |>
    else spi with err := T
  | init_done => spi with err := T`

(* write a value to spi.regs.CH0CONF with WL bit *)
val write_CH0CONF_WL_def = Define `
write_CH0CONF_WL (value:word32) (spi:spi_state) =
let v = (11 >< 7) value:word5 in
case spi.init.state of
  | init_start => spi with err := T
  | init_reset => spi with err := T
  | init_setregs => if v >+ 2w then 
  spi with <|regs := spi.regs with 
  CH0CONF := spi.regs.CH0CONF with WL := v;
  init := spi.init with <|ch0conf_wordlen_done := T;
  state := if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
  /\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done 
  /\ spi.init.ch0conf_speed_done) then init_done else init_setregs |> |>
  else spi with err := T
  | init_done => spi with err := T`

(*if (v <=+ 2w) \/ (spi.tx.state <> tx_idle) \/ (spi.rx.state <> rx_idle) then spi with err := T 
  else spi with <|regs := spi.regs with
  CH0CONF := spi.regs.CH0CONF with WL := v|>`*)

(* write a value to spi.regs.CH0CONF to set mode, 
   including IS, DPE1, DPE0, TRM, EPOL, POL, PHA bits *)
val write_CH0CONF_mode_def = Define `
write_CH0CONF_mode (value:word32) (spi:spi_state) =
let v1 = (18 >< 18) value:word1 and
v2 = (17 >< 17) value:word1 and
v3 = (16 >< 16) value:word1 and
v4 = (13 >< 12) value:word2 and
v5 = (6 >< 6) value:word1 and
v6 = (1 >< 1) value:word1 and
v7 = (0 >< 0) value:word1 in
case spi.init.state of
  | init_start => spi with err := T
  | init_reset => spi with err := T
  | init_setregs => if v4 = 3w then spi with err := T
    else spi with <|regs := spi.regs with
    CH0CONF := spi.regs.CH0CONF with <|IS := v1; DPE1 := v2; DPE0 := v3;
    TRM := v4; EPOL := v5; POL := v6; PHA := v7|>;
    init := spi.init with <|ch0conf_mode_done := T;
    state := if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
    /\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done 
    /\ spi.init.ch0conf_speed_done) then init_done else init_setregs |> |>
  | init_done => spi with err := T`

(* write a value to spi.regs.CH0CONF to set speed *)
val write_CH0CONF_speed_def = Define `
write_CH0CONF_speed (value:word32) (spi:spi_state) =
let v = (5 >< 2) value:word4 in
case spi.init.state of
  | init_start => spi with err := T
  | init_reset => spi with err := T
  | init_setregs => spi with <|regs := spi.regs with
    CH0CONF := spi.regs.CH0CONF with CLKD := v;
    init := spi.init with <|ch0conf_speed_done := T;
    state := if (spi.init.sysconfig_mode_done /\ spi.init.modulctrl_bus_done 
    /\ spi.init.ch0conf_wordlen_done /\ spi.init.ch0conf_mode_done 
    /\ spi.init.ch0conf_speed_done) then init_done else init_setregs |> |>
  | init_done => spi with err := T`

(* write a value to spi.regs.CH0CONF to start and finish the tx process, 
   vaild when TRM = 2 *)
val write_CH0CONF_tx_def = Define `
write_CH0CONF_tx (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
v2 = (20 >< 20) value:word1 in
case spi.tx.state of
  | tx_idle => if ((spi.init.state = init_done) /\ (spi.rx.state = rx_idle) 
               /\ (spi.xfer.state = xfer_idle) /\ (v1 = 2w) /\ (v2 = 1w)) then 
    spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF
    with <|TRM := 2w; FORCE := 1w |>;
    tx := spi.tx with state := tx_conf_ready|> 
    else spi with err := T
  | tx_conf_ready => spi with err := T
  | tx_channel_enabled => spi with err := T
  | tx_issue_mem_req => spi with err := T
  | tx_mem_reply => spi with err := T
  | tx_done => spi with err := T
  | tx_disable_channel =>  spi with err := T
  | tx_reset_conf => if (spi.init.state = init_done) /\ (spi.rx.state = rx_idle)
                         /\ (spi.xfer.state = xfer_idle) /\ (v2 = 0w) then
    spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF 
    with FORCE := 0w;
    tx := spi.tx with state := tx_idle|>
    else spi with err := T`

(* enable or disable the SPI channel 0 for tx, rx and xfer *)
val write_CH0CTRL_def = Define `
write_CH0CTRL (value:word32) (spi:spi_state) =
let v = (0 >< 0) value:word1 in
if (spi.init.state = init_done) /\ (spi.tx.state = tx_conf_ready) /\ 
   (spi.rx.state = rx_idle) /\ (spi.xfer.state = xfer_idle) /\ (v = 1w) 
then spi with <|regs := spi.regs with CH0CTRL := 1w; 
tx := spi.tx with state := tx_channel_enabled |>
else if (spi.init.state = init_done) /\ (spi.tx.state = tx_disable_channel) /\
     (spi.rx.state = rx_idle) /\ (spi.xfer.state = xfer_idle) /\ (v = 0w)
then spi with <|regs := spi.regs with CH0CTRL := 0w;
tx := spi.tx with state := tx_reset_conf |>
else if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
        (spi.rx.state = rx_conf_ready) /\ (spi.xfer.state = xfer_idle) 
        /\ (v = 1w)
then spi with <|regs := spi.regs with CH0CTRL := 1w;
rx := spi.rx with state := rx_channel_enabled |>
else if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
        (spi.rx.state = rx_disable_channel) /\ (spi.xfer.state = xfer_idle)
        /\ (v = 0w)
then spi with <|regs := spi.regs with CH0CTRL := 0w;
rx := spi.rx with state := rx_reset_conf|>
else if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
        (spi.rx.state = rx_idle) /\ (spi.xfer.state = xfer_conf_ready) 
        /\ (v = 1w)
then spi with <|regs := spi.regs with CH0CTRL := 1w;
xfer := spi.xfer with state := xfer_channel_enabled |>
else if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
        (spi.rx.state = rx_idle) /\ (spi.xfer.state = xfer_disable_channel)
        /\ (v = 0w)
then spi with <|regs := spi.regs with CH0CTRL := 0w;
xfer := spi.xfer with state := xfer_reset_conf|>
else spi with err := T`

(* write the spi.regs.CH0CONF to start and finish the rx process, vaild when TRM = 1 *)
val write_CH0CONF_rx_def = Define `
write_CH0CONF_rx (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
v2 = (20 >< 20) value:word1 in
case spi.rx.state of
  | rx_idle => if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
                  (spi.xfer.state = xfer_idle) /\ (v1 = 1w) /\ (v2 = 1w) then
    spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF
    with <|TRM := 1w; FORCE := 1w|>;
    rx := spi.rx with state := rx_conf_ready |>
    else spi with err := T
  | rx_conf_ready => spi with err := T
  | rx_channel_enabled => spi with err := T
  | rx_issue_write_mem_req => spi with err := T
  | rx_check => spi with err := T
  | rx_disable_channel => spi with err := T
  | rx_reset_conf => if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle)
                        /\ (spi.xfer.state = xfer_idle) /\ (v2 = 0w) then
    spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF 
               with FORCE := 0w;
               rx := spi.rx with state := rx_idle|>
    else spi with err := T`

(* write the spi.regs.CH0CONF to start and finish the xfer process, vaild when TRM = 0 *)
val write_CH0CONF_xfer_def = Define `
write_CH0CONF_xfer (value:word32) (spi:spi_state) =
let v1 = (13 >< 12) value:word2 and
v2 = (20 >< 20) value:word1 in
case spi.xfer.state of
  | xfer_idle => if (spi.init.state = init_done) /\ (spi.tx.state = tx_idle) /\
                    (spi.rx.state = rx_idle) /\ (v1 = 0w) /\ (v2 = 1w) then
   spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF
   with  <|TRM := 0w; FORCE := 1w |>;
   xfer := spi.xfer with state := xfer_conf_ready|>
   else spi with err := T
  | xfer_conf_enabled => spi with err := T
  | xfer_channel_enabled => spi with err := T
  | xfer_issue_mem_req => spi with err := T
  | xfer_mem_reply => spi with err := T
  | xfer_issue_write_mem_req => spi with err := T
  | xfer_check => spi with err := T
  | xfer_disable_channel => spi with err := T
  | xfer_reset_conf => if (spi.init.state = init_done) /\ 
    (spi.tx.state = tx_idle) /\ (spi.rx.state = rx_idle) /\ (v2 = 0w) then
    spi with <|regs := spi.regs with CH0CONF := spi.regs.CH0CONF 
               with FORCE := 0w;
               xfer := spi.xfer with state := xfer_idle|>
    else spi with err := T`

(* write_SPI_regs_def:word32 -> word32 -> spi_state *)
val write_SPI_regs_def = Define `
write_SPI_regs (pa:word32) (value:word32) (spi:spi_state) =
if spi.err then spi
else if ~(pa IN SPI0_PA_RANGE) then spi with err := T
else if (pa = SPI0_SYSCONFIG) /\ (value = 2w) then (write_SOFTRESET value spi)
else if (pa = SPI0_SYSCONFIG) /\ ((0 >< 0) value:word1 = 1w) 
then (write_SYSCONFIG_mode value spi)
else if (pa = SPI0_MODULCTRL) then (write_MODULCTRL value spi)
else if (pa = SPI0_CH0CONF) /\ ((11 >< 7) value:word5 <> 0w)
then (write_CH0CONF_WL value spi)
else if (pa = SPI0_CH0CONF) /\ ((17 >< 16) value:word2 <> 0w)
then (write_CH0CONF_mode value spi)
else if (pa = SPI0_CH0CONF) /\ (value = 0w \/ ((5 >< 2) value:word4 <> 0w))
then (write_CH0CONF_speed value spi)
else if (pa = SPI0_CH0CONF) /\ (((13 >< 12) value:word2 = 2w) \/ (value = 0w /\ spi.tx.state = tx_reset_conf)) then (write_CH0CONF_tx value spi)
else if (pa = SPI0_CH0CONF) /\ (((13 >< 12) value:word2 = 1w) \/ (value = 0w /\ spi.rx.state = rx_reset_conf)) then (write_CH0CONF_rx value spi)
else if (pa = SPI0_CH0CONF) /\ ((((13 >< 12) value:word2 = 0w) /\ ((20 >< 20) value:word1 = 1w)) \/ (value = 0w /\ spi.xfer.state = xfer_reset_conf)) then
(write_CH0CONF_xfer value spi)
else if (pa = SPI0_CH0CTRL) then (write_CH0CTRL value spi)
else spi`

val _ = export_theory();
