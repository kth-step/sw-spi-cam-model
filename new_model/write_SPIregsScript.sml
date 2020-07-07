open HolKernel bossLib boolLib Parse;
open wordsTheory wordsLib;
open SPI_stateTheory board_memTheory;

val _ = new_theory "write_SPIregs";

(* write a value(1) to spi.regs.SYSCONFIG.SOFTRESET, start the reset process 
 * write_SOFTRESET: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_SOFTRESET_def = Define `
write_SOFTRESET (value:word32) (spi:spi_state) (driver:spi_driver) =
let v = (1 >< 1) value :word1 in
case driver.init.state of
| init_start => if v = 0w then (spi with err := T, driver)
  else (spi with regs := spi.regs with 
            SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 1w,
        driver with init := driver.init with 
                  <|state := init_reset; 
                    sysconfig_mode_done := F; 
                    modulctrl_bus_done := F; 
                    ch0conf_wordlen_done := F; 
                    ch0conf_mode_done := F;
                    ch0conf_speed_done := F |>)
| init_reset => (spi with err := T, driver)
| init_setregs => (spi with err := T, driver)
| init_done => 
  if ((v = 1w) /\ (driver.tx.state <> tx_idle \/ driver.rx.state <> rx_idle)) 
  then (spi with err:= T, driver)
  else if v = 1w then 
  (spi with regs := spi.regs with 
       SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 1w,
   driver with init := driver.init with 
                  <|state := init_reset; 
                    sysconfig_mode_done := F; 
                    modulctrl_bus_done:= F; 
                    ch0conf_wordlen_done := F; 
                    ch0conf_wordlen_done := F |>)
  else (spi, driver)`

(* write a value to spi.regs.SYSCONFIG, set some bits of SYSCONFIG 
 * write_SYSCONFIG_def: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_SYSCONFIG_def = Define `
write_SYSCONFIG (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (0 >< 0) value:word1 and
    v2 = (4 >< 3) value: word2 in
case driver.init.state of
  | init_start => (spi with err := T, driver)
  | init_reset => (spi with err := T, driver)
  | init_setregs => if ((v1 = 1w) /\ (v2 = 2w)) then
   (spi with regs := spi.regs with 
    SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>,
    driver with init := driver.init with 
    <|sysconfig_mode_done := T;
      state := if (driver.init.sysconfig_mode_done /\ driver.init.modulctrl_bus_done 
      /\ driver.init.ch0conf_wordlen_done /\ driver.init.ch0conf_mode_done 
      /\ driver.init.ch0conf_speed_done) then init_done else init_setregs|>) 
    else (spi with err := T, driver)
  | init_done => (spi with err := T, driver)`

(* write a value to spi.regs.MODULCTRL, set to a single-channel master mode
 * write_MODULCTRL: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_MODULCTRL_def = Define `
write_MODULCTRL (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (0 >< 0) value: word1 and
    v2 = (2 >< 2) value: word1 and
    v3 = (3 >< 3) value: word1 in
case driver.init.state of
  | init_start => (spi with err := T,driver) 
  | init_reset => (spi with err := T,driver)
  | init_setregs => if ((v1 = 1w) /\ (v2 = 0w) /\ (v3 = 0w)) then
   (spi with regs := spi.regs with MODULCTRL := spi.regs.MODULCTRL with
        <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>,
    driver with init := driver.init with <| modulctrl_bus_done := T;
      state := if (driver.init.sysconfig_mode_done /\ driver.init.modulctrl_bus_done 
      /\ driver.init.ch0conf_wordlen_done /\ driver.init.ch0conf_mode_done 
      /\ driver.init.ch0conf_speed_done) then init_done else init_setregs|>)
    else (spi with err := T, driver)
  | init_done => (spi with err := T, driver)`

(* write a value to spi.regs.CH0CONF with WL bit 
 * write_CH0CONF_WL: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_WL_def = Define `
write_CH0CONF_WL (value:word32) (spi:spi_state) (driver:spi_driver) =
let v = (11 >< 7) value:word5 in
case driver.init.state of
  | init_start => (spi with err := T, driver)
  | init_reset => (spi with err := T, driver)
  | init_setregs => if v >+ 2w then 
  (spi with regs := spi.regs with 
   CH0CONF := spi.regs.CH0CONF with WL := v,
   driver with init := driver.init with <|ch0conf_wordlen_done := T;
   state := if (driver.init.sysconfig_mode_done /\ driver.init.modulctrl_bus_done 
   /\ driver.init.ch0conf_wordlen_done /\ driver.init.ch0conf_mode_done 
   /\ driver.init.ch0conf_speed_done) then init_done else init_setregs |>)
  else (spi with err := T, driver)
  | init_done => (spi with err := T, driver)`

(* write a value to spi.regs.CH0CONF to set mode, 
   including IS, DPE1, DPE0, TRM, EPOL, POL, PHA bits
 * write_CH0CONF: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_def = Define `
write_CH0CONF (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (18 >< 18) value:word1 and
    v2 = (17 >< 17) value:word1 and
    v3 = (16 >< 16) value:word1 and
    v4 = (13 >< 12) value:word2 and
    v5 = (6 >< 6) value:word1 and
    v6 = (1 >< 1) value:word1 and
    v7 = (0 >< 0) value:word1 in
case driver.init.state of
  | init_start => (spi with err := T, driver)
  | init_reset => (spi with err := T, driver)
  | init_setregs => if v4 = 3w then (spi with err := T, driver)
    else (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF with 
              <|IS := v1; DPE1 := v2; DPE0 := v3;
                TRM := v4; EPOL := v5; POL := v6; PHA := v7|>,
          driver with init := driver.init with <|ch0conf_mode_done := T;
          state := 
    if (driver.init.sysconfig_mode_done /\ driver.init.modulctrl_bus_done 
     /\ driver.init.ch0conf_wordlen_done /\ driver.init.ch0conf_mode_done 
     /\ driver.init.ch0conf_speed_done) then init_done else init_setregs |>)
  | init_done => (spi with err := T, driver)`

(* write a value to spi.regs.CH0CONF to set speed 
 * write_CH0CONF_speed: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_speed_def = Define `
write_CH0CONF_speed (value:word32) (spi:spi_state) (driver:spi_driver) =
let v = (5 >< 2) value:word4 in
case driver.init.state of
  | init_start => (spi with err := T, driver)
  | init_reset => (spi with err := T, driver)
  | init_setregs => 
    (spi with regs := spi.regs with
     CH0CONF := spi.regs.CH0CONF with CLKD := v,
     driver with init := driver.init with <|ch0conf_speed_done := T;
     state := if (driver.init.sysconfig_mode_done /\ driver.init.modulctrl_bus_done 
     /\ driver.init.ch0conf_wordlen_done /\ driver.init.ch0conf_mode_done 
     /\ driver.init.ch0conf_speed_done) then init_done else init_setregs |>)
  | init_done => (spi with err := T, driver)`

(* enable or disable the SPI channel 0 for tx, rx and xfer
 * write_CH0CTRL: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CTRL_def = Define `
write_CH0CTRL (value:word32) (spi:spi_state) (driver: spi_driver) =
let v = (0 >< 0) value:word1 in
if (driver.init.state = init_done) /\ (driver.tx.state = tx_conf_ready) /\ 
   (driver.rx.state = rx_idle) /\ (driver.xfer.state = xfer_idle) /\ (v = 1w) 
then (spi with regs := spi.regs with CH0CTRL := 1w, 
      driver with tx := driver.tx with state := tx_channel_enabled)
else if (driver.init.state = init_done) /\ (driver.tx.state = tx_disable_channel) /\
     (driver.rx.state = rx_idle) /\ (driver.xfer.state = xfer_idle) /\ (v = 0w)
then (spi with regs := spi.regs with CH0CTRL := 0w,
      driver with tx := driver.tx with state := tx_reset_conf)
else if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
        (driver.rx.state = rx_conf_ready) /\ (driver.xfer.state = xfer_idle) 
        /\ (v = 1w)
then (spi with regs := spi.regs with CH0CTRL := 1w,
      driver with rx := driver.rx with state := rx_channel_enabled)
else if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
        (driver.rx.state = rx_disable_channel) /\ (driver.xfer.state = xfer_idle)
        /\ (v = 0w)
then (spi with regs := spi.regs with CH0CTRL := 0w,
      driver with rx := driver.rx with state := rx_reset_conf)
else if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
        (driver.rx.state = rx_idle) /\ (driver.xfer.state = xfer_conf_ready) 
        /\ (v = 1w)
then (spi with regs := spi.regs with CH0CTRL := 1w,
      driver with xfer := driver.xfer with state := xfer_channel_enabled)
else if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
        (driver.rx.state = rx_idle) /\ (driver.xfer.state = xfer_disable_channel)
        /\ (v = 0w)
then (spi with regs := spi.regs with CH0CTRL := 0w,
      driver with xfer := driver.xfer with state := xfer_reset_conf)
else (spi with err := T, driver)`


(* write a value to spi.regs.CH0CONF to start and finish the tx process, vaild when TRM = 2.
 * write_CH0CONF_tx: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_tx_def = Define `
write_CH0CONF_tx (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case driver.tx.state of
  | tx_idle => if ((driver.init.state = init_done) /\ (driver.rx.state = rx_idle) 
               /\ (driver.xfer.state = xfer_idle) /\ (v1 = 2w) /\ (v2 = 1w)) then 
   (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF
    with <|TRM := 2w; FORCE := 1w |>,
    driver with tx := driver.tx with state := tx_conf_ready) 
    else (spi with err := T, driver)
  | tx_conf_ready => (spi with err := T, driver)
  | tx_channel_enabled => (spi with err := T, driver)
  | tx_issue_mem_req => (spi with err := T, driver)
  | tx_mem_reply => (spi with err := T, driver)
  | tx_done => (spi with err := T, driver)
  | tx_disable_channel =>  (spi with err := T, driver)
  | tx_reset_conf => if (driver.init.state = init_done) /\ (driver.rx.state = rx_idle)
                         /\ (driver.xfer.state = xfer_idle) /\ (v2 = 0w) then
   (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF with FORCE := 0w,
    driver with tx := driver.tx with state := tx_idle)
    else (spi with err := T, driver)`

(* write the spi.regs.CH0CONF to start and finish the rx process, vaild when TRM = 1. 
 * write_CH0CONF_rx: word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_rx_def = Define `
write_CH0CONF_rx (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case driver.rx.state of
  | rx_idle => if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
                  (driver.xfer.state = xfer_idle) /\ (v1 = 1w) /\ (v2 = 1w) then
   (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF
    with <|TRM := 1w; FORCE := 1w|>,
    driver with rx := driver.rx with state := rx_conf_ready)
    else (spi with err := T, driver)
  | rx_conf_ready => (spi with err := T, driver)
  | rx_channel_enabled => (spi with err := T, driver)
  | rx_issue_write_mem_req => (spi with err := T, driver)
  | rx_check => (spi with err := T, driver)
  | rx_disable_channel => (spi with err := T, driver)
  | rx_reset_conf => if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle)
                        /\ (driver.xfer.state = xfer_idle) /\ (v2 = 0w) then
   (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF with FORCE := 0w,
    driver with rx := driver.rx with state := rx_idle)
    else (spi with err := T, driver)`

(* write the spi.regs.CH0CONF to start and finish the xfer process, vaild when TRM = 0 
 * write_CH0CONF_xfer:word32 -> spi_state -> spi_driver -> spi_state * spi_driver
 *)
val write_CH0CONF_xfer_def = Define `
write_CH0CONF_xfer (value:word32) (spi:spi_state) (driver:spi_driver) =
let v1 = (13 >< 12) value:word2 and
    v2 = (20 >< 20) value:word1 in
case driver.xfer.state of
  | xfer_idle => if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) /\
                    (driver.rx.state = rx_idle) /\ (v1 = 0w) /\ (v2 = 1w) then
  (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF
   with  <|TRM := 0w; FORCE := 1w |>,
   driver with xfer := driver.xfer with state := xfer_conf_ready)
   else (spi with err := T, driver)
  | xfer_conf_enabled => (spi with err := T, driver)
  | xfer_channel_enabled => (spi with err := T, driver)
  | xfer_issue_mem_req => (spi with err := T, driver)
  | xfer_mem_reply => (spi with err := T, driver)
  | xfer_issue_write_mem_req => (spi with err := T, driver)
  | xfer_check => (spi with err := T, driver)
  | xfer_disable_channel => (spi with err := T, driver)
  | xfer_reset_conf => if (driver.init.state = init_done) /\ (driver.tx.state = tx_idle) 
                       /\ (driver.rx.state = rx_idle) /\ (v2 = 0w) then
   (spi with regs := spi.regs with CH0CONF := spi.regs.CH0CONF  with FORCE := 0w,
    driver with xfer := driver.xfer with state := xfer_idle)
    else (spi with err := T, driver)`

(* write_TX0: word32 -> spi_state -> spi_driver -> spi_state * spi_driver *)
val write_TX0_def = Define `
write_TX0 (value:word32) (spi:spi_state) =
let wl = (w2n spi.regs.CH0CONF.WL) + 1 in
if (CHECK_TXS_BIT spi) /\ (spi.regs.CH0CONF.WL >+ 3w) then
spi with regs := spi.regs with TX0 := ((wl >< 0) value:word32)
else spi with err := T`

(* write_SPI_regs_def:word32 -> word32 -> spi_state -> spi_driver -> spi_state * spi_driver *)
val write_SPI_regs_def = Define `
write_SPI_regs (pa:word32) (value:word32) (spi:spi_state) (driver:spi_driver) =
if spi.err then (spi,driver)
else if ~(pa IN SPI0_PA_RANGE) then (spi with err := T, driver)
else if (pa = SPI0_SYSCONFIG) /\ (value = 2w) 
then (write_SOFTRESET value spi driver)
else if (pa = SPI0_SYSCONFIG) /\ ((0 >< 0) value:word1 = 1w) 
then (write_SYSCONFIG value spi driver)
else if (pa = SPI0_MODULCTRL) then (write_MODULCTRL value spi driver)
else if (pa = SPI0_CH0CONF) /\ ((11 >< 7) value:word5 <> 0w)
then (write_CH0CONF_WL value spi driver)
else if (pa = SPI0_CH0CONF) /\ ((17 >< 16) value:word2 <> 0w)
then (write_CH0CONF value spi driver)
else if (pa = SPI0_CH0CONF) /\ (value = 0w \/ ((5 >< 2) value:word4 <> 0w))
then (write_CH0CONF_speed value spi driver)
else if (pa = SPI0_CH0CONF) /\ (((13 >< 12) value:word2 = 2w) \/ (value = 0w /\ driver.tx.state = tx_reset_conf)) then (write_CH0CONF_tx value spi driver)
else if (pa = SPI0_CH0CONF) /\ (((13 >< 12) value:word2 = 1w) \/ (value = 0w /\ driver.rx.state = rx_reset_conf)) then (write_CH0CONF_rx value spi driver)
else if (pa = SPI0_CH0CONF) /\ ((((13 >< 12) value:word2 = 0w) /\ ((20 >< 20) value:word1 = 1w)) \/ (value = 0w /\ driver.xfer.state = xfer_reset_conf)) then
(write_CH0CONF_xfer value spi driver)
else if (pa = SPI0_CH0CTRL) then (write_CH0CTRL value spi driver)
else if (pa = SPI0_TX0) then (write_TX0 value spi, driver)
(* RX0 and CH0STAT are read-only *)
else if (pa = SPI0_RX0) then (spi, driver)
else if (pa = SPI0_CH0STAT) then (spi, driver) 
(* write to non-modeled address in SPI, no changes *)
else (spi, driver)`

val _ = export_theory();
