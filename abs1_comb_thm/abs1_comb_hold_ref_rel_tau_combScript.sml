open HolKernel bossLib boolLib Parse wordsLib wordsTheory;
open SPI_stateTheory SPI_relationTheory weak_bisimulationTheory SPI_tauTheory SPI_update_regsTheory SPI_return_regsTheory driver_stateTheory driver_relationTheory driver_writeTheory driver_readTheory driver_checkTheory ds_abs1_stateTheory ds_abs1_relTheory ds_abs1_initTheory ds_abs1_txTheory ds_abs1_rxTheory ds_abs1_xferTheory ref_relTheory board_memTheory;

val _ = new_theory "abs1_comb_hold_ref_rel_tau_comb";

(* a basic theorem for word1: if it is not 1w, then it is 0w *)
val word1_not_1w_eq_0w = store_thm("word1_not_1w_eq_0w",
``!w:word1. w <> 1w:word1 ==> w = 0w:word1``,
Cases_on `w` >> rw [] >>
FULL_SIMP_TAC (arith_ss++WORD_ss) []);

(* related to init automaton *)
(* dr.state = dr_init_setting and spi.state = init_setregs, 1 step before the final one *)
val n_tau_tr_dr_init_setting_1 = store_thm("n_tau_tr_dr_init_setting_1",
``!dr spi. 
dr.state = dr_init_setting /\ spi.state = init_setregs /\
dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\ 
spi.regs.CH0CONF.WL = 0w /\ spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w ==>
n_tau_tr 1 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_init := dr.dr_init with issue_wr_modulctrl := T |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := spi.init with modulctrl_bus_done := T |>)``, 
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`(dr_write_state dr = dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_modulctrl := T |>) /\
(dr_write_address dr = SOME SPI0_MODULCTRL) /\
(dr_write_value dr = SOME (0x00000001w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w spi = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>; 
init := spi.init with modulctrl_bus_done := T |>)`
by fs [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_modulctrl := T |>) = 
dr with <|state := dr_ready;
dr_init := dr.dr_init with issue_wr_modulctrl := T |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_modulctrl := T |>) = SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_modulctrl := T |>) = SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs:= spi.regs with MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
init := spi.init with modulctrl_bus_done := T |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_setting and spi.state = init_setregs, 2 steps before the final one *)
val n_tau_tr_dr_init_setting_2 = store_thm("n_tau_tr_dr_init_setting_2",
``!dr spi. 
dr.state = dr_init_setting /\ spi.state = init_setregs /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\
spi.regs.CH0CONF.WL = 0w /\ spi.regs.CH0CONF.IS = 1w /\ 
spi.regs.CH0CONF.FORCE = 0w ==>
n_tau_tr 2 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T |> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>)``, 
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`(dr_write_state dr = dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address dr = SOME SPI0_SYSCONFIG) /\
(dr_write_value dr = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w spi = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := spi.init with <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs:= spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with 
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_check_rep and spi.state = init_setregs, last_read_v = 1w *)
val n_tau_tr_dr_init_check_rep_3 = store_thm("n_tau_tr_dr_init_check_rep_3",
``!dr spi v. 
dr.state = dr_init_check_rep /\ spi.state = init_setregs /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\
dr.dr_last_read_ad = SOME SPI0_SYSSTATUS /\ dr.dr_last_read_v = SOME v /\
(0 >< 0) v:word1 = 1w /\ spi.regs.CH0CONF.WL = 0w /\ 
spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w ==>
n_tau_tr 3 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_init := 
<|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``,
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_SYSSTATUS v = dr with state := dr_init_setting` 
by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with state := dr_init_setting) = 
dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address (dr with state := dr_init_setting) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with state := dr_init_setting) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w spi = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := spi.init with <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs:= spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with 
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_read_req and spi.state = init_setregs *)
val n_tau_tr_dr_init_read_req_4 = store_thm("n_tau_tr_dr_init_read_req_4",
``!dr spi. 
dr.state = dr_init_read_req /\ spi.state = init_setregs /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\
spi.regs.SYSSTATUS = 1w /\ spi.regs.CH0CONF.WL = 0w /\ 
spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w  ==>
n_tau_tr 4 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``, 
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS |>` by rw [dr_read_def, dr_read_sysstatus_def] >> rw [] >>
`read_SPI_regs_state SPI0_SYSSTATUS spi = spi /\
read_SPI_regs_value SPI0_SYSSTATUS spi = w2w spi.regs.SYSSTATUS` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_SYSSTATUS_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def] >> rw [] >>
`dr_check (dr with <|state := dr_init_check_rep; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) SPI0_SYSSTATUS 1w =
dr with <|state := dr_init_setting; dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>` by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w spi = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := spi.init with <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs:= spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with 
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_check_rep and spi.state = init_setregs, last_read_v = 0w *)
val n_tau_tr_dr_init_check_rep_5 = store_thm("n_tau_tr_dr_init_check_rep_5",
``!dr spi v. 
dr.state = dr_init_check_rep /\ spi.state = init_setregs /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\
spi.regs.SYSSTATUS = 1w /\ spi.regs.CH0CONF.WL = 0w /\ 
spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w /\
dr.dr_last_read_ad = SOME SPI0_SYSSTATUS /\ dr.dr_last_read_v = SOME v /\ 
(0 >< 0) v:word1 = 0w ==>
n_tau_tr 5 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``,
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_SYSSTATUS v = dr with state := dr_init_read_req` 
by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`dr_read (dr with state := dr_init_read_req) = dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS |>` by rw [dr_read_def, dr_read_sysstatus_def] >> rw [] >>
`read_SPI_regs_state SPI0_SYSSTATUS spi = spi /\
read_SPI_regs_value SPI0_SYSSTATUS spi = w2w spi.regs.SYSSTATUS` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_SYSSTATUS_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def] >> rw [] >>
`dr_check (dr with <|state := dr_init_check_rep; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) SPI0_SYSSTATUS 1w =
dr with <|state := dr_init_setting; dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>` by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w spi = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; regs := spi.regs with 
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := spi.init with <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs:= spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with 
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_read_req and spi.state = init_reset *)
val n_tau_tr_dr_init_read_req_5 = store_thm("n_tau_tr_dr_init_read_req_5",
``!dr spi. 
dr.state = dr_init_read_req /\ spi.state = init_reset /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done ==>
n_tau_tr 5 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := 
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``, 
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
Q.EXISTS_TAC `(dr,spi_tau_operations spi)` >> rw [] >>
`spi_tau_operations spi = spi with <|regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
state := init_setregs |>` by rw [spi_tau_operations_def, init_reset_op_def] >> rw [] >>
`dr_read dr = dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS |>` by rw [dr_read_def, dr_read_sysstatus_def] >> rw [] >>
`(read_SPI_regs_state SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 
(spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>)) /\
(read_SPI_regs_value SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 1w:word32)` 
by rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_SYSSTATUS_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def] >> rw [] >>
`dr_check (dr with <|state := dr_init_check_rep; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) SPI0_SYSSTATUS 1w =
dr with <|state := dr_init_setting; dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>` by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 
(spi with <|state := init_setregs; 
regs := spi.regs with  <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|>;
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|> |>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; 
regs := spi.regs with 
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS = 1w` by fs [] >>
`(19 >< 19) (66520w:word32):word1 <> ((spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS)` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_check_rep and spi.state = init_reset *)
val n_tau_tr_dr_init_check_rep_6 = store_thm("n_tau_tr_dr_init_check_rep_6",
``!dr spi v. 
dr.state = dr_init_check_rep /\ spi.state = init_reset /\
~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done /\
dr.dr_last_read_ad = SOME SPI0_SYSSTATUS /\ dr.dr_last_read_v = SOME v /\
(0 >< 0) v:word1 = 0w ==>
n_tau_tr 6 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T |> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``, 
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
Q.EXISTS_TAC `(dr_check dr SPI0_SYSSTATUS v,spi)` >> rw [] >>
`dr_check dr SPI0_SYSSTATUS v = dr with state := dr_init_read_req` by rw [dr_check_def, dr_check_sysstatus_def] >>
rw [GSYM LEFT_EXISTS_AND_THM] >>
Q.EXISTS_TAC `(dr with state := dr_init_read_req, spi_tau_operations spi)` >> rw [] >>
`spi_tau_operations spi = spi with <|regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
state := init_setregs |>` by rw [spi_tau_operations_def, init_reset_op_def] >> rw [] >>
`dr_read (dr with state := dr_init_read_req) = dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS |>` by rw [dr_read_def, dr_read_sysstatus_def] >> rw [] >>
`(read_SPI_regs_state SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 
(spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>)) /\
(read_SPI_regs_value SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 1w:word32)` 
by rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_SYSSTATUS_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def] >> rw [] >>
`dr_check (dr with <|state := dr_init_check_rep; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) SPI0_SYSSTATUS 1w =
dr with <|state := dr_init_setting; dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>` by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) /\
(dr_write_address (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w|>) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w (spi with <|state := init_setregs;
regs := spi.regs with <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |> |>) = 
(spi with <|state := init_setregs; 
regs := spi.regs with  <|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|>;
SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|> |>; 
init := spi.init with sysconfig_mode_done := T |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = 
dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T |> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with issue_wr_sysconfig := T |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; 
regs := spi.regs with 
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>; 
init := spi.init with sysconfig_mode_done := T |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS = 1w` by fs [] >>
`(19 >< 19) (66520w:word32):word1 <> ((spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS)` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with
<|SIDLEMODE := 2w; AUTOIDLE := 1w|>; SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* dr.state = dr_init_idle and spi.state = init_start or spi_ready *)
val n_tau_tr_dr_init_idle_6 = store_thm("n_tau_tr_dr_init_check_rep_6",
``!dr spi. 
dr.state = dr_init_idle /\ (spi.state = init_start \/ spi.state = spi_ready) ==>
n_tau_tr 6 local_tr (dr,spi) tau 
(dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>, 
spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)``,
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, GSYM LEFT_EXISTS_AND_THM] >>
`(dr_write_state dr = dr with <| state := dr_init_read_req;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) /\
(dr_write_address dr =  SOME SPI0_SYSCONFIG) /\
(dr_write_value dr = SOME (0x00000002w:word32))` 
by rw [dr_write_state_def, dr_write_value_def, dr_write_address_def,
dr_write_def, dr_write_softreset_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 2w spi =
spi with <| regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; SYSSTATUS := 0w |>;
state := init_reset;
init := <| sysconfig_mode_done := F; modulctrl_bus_done := F |> |>` 
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SOFTRESET_def] >> rw [] >>
Q.EXISTS_TAC `(dr with <| state := dr_init_read_req; 
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>, 
spi_tau_operations (spi with <|state := init_reset; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; SYSSTATUS := 0w|>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>))` >> rw [] >>
`spi_tau_operations (spi with <|state := init_reset; regs := spi.regs with
<|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; SYSSTATUS := 0w|>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>) = 
spi with <|regs := spi.regs with 
<|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w; SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|>;
state := init_setregs |>` by rw [spi_tau_operations_def, init_reset_op_def] >> rw [] >>
`dr_read (dr with <|state := dr_init_read_req; 
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) = 
dr with <| state := dr_init_check_rep;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>` 
by rw [dr_read_def, dr_read_sysstatus_def] >> rw [] >>
`(read_SPI_regs_state SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>) = 
(spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>)) /\
(read_SPI_regs_value SPI0_SYSSTATUS (spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>) = 1w:word32)` 
by rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_SYSSTATUS_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def] >> rw [] >>
`dr_check (dr with <|state := dr_init_check_rep; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) SPI0_SYSSTATUS 1w =
dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>` 
by rw [dr_check_def, dr_check_sysstatus_def] >> rw [] >>
`(dr_write_state (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) = 
dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := F|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) = SOME SPI0_SYSCONFIG) /\
(dr_write_value (dr with <|state := dr_init_setting; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := F; issue_wr_modulctrl := F|> |>) = SOME (0x00000011w:word32))` 
by rw [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_sysconfig_def] >> rw [] >>
`write_SPI_regs SPI0_SYSCONFIG 17w (spi with <|state := init_setregs;
regs := spi.regs with <|SYSCONFIG := spi.regs.SYSCONFIG with SOFTRESET := 0w;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := F; modulctrl_bus_done := F|> |>) = 
(spi with <|state := init_setregs; 
regs := spi.regs with 
<|SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|>;
SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|> |>; 
init := <|sysconfig_mode_done := T; modulctrl_bus_done := F|> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, write_SYSCONFIG_comb_def, write_SYSCONFIG_def] >> rw [] >>
`(dr_write_state (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := F|> |>) = 
dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := dr.dr_init with 
<|issue_wr_sysconfig := T ; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := F|> |>) = SOME SPI0_MODULCTRL) /\
(dr_write_value (dr with <| state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := F|> |>) = SOME (0x00000001w))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_modulctrl_def] >> rw [] >>
`~(0w:word5 >+ 2w:word5)` by EVAL_TAC >>
`write_SPI_regs SPI0_MODULCTRL 1w 
(spi with <|state := init_setregs; 
regs := spi.regs with 
<|SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>; 
init := <|sysconfig_mode_done := T; modulctrl_bus_done := F |> |>) =
(spi with <|state := init_setregs; regs := spi.regs with
<|SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w; 
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)`
by rw [write_SPI_regs_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, write_MODULCTRL_def] >> fs [] >>
`(dr_write_state (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) = 
dr with <|state := dr_ready;
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>) /\
(dr_write_address (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T ; issue_wr_modulctrl := T|> |>) = 
SOME SPI0_CH0CONF) /\
(dr_write_value (dr with <|state := dr_init_setting;
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T ; issue_wr_modulctrl := T|> |>) = 
SOME (66520w:word32))` 
by fs [dr_write_state_def, dr_write_address_def, dr_write_value_def,
dr_write_def, dr_write_ch0conf_init_def] >> fs [] >>
`(spi with <|state := init_setregs;
regs := spi.regs with <|
SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>; 
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS = 1w` by fs [] >>
`(19 >< 19) (66520w:word32):word1 <> ((spi with <|state := init_setregs;
regs := spi.regs with <|
SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>; 
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>).regs.CH0CONF.IS)` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) 
(spi with <|state := init_setregs;
regs := spi.regs with <|
SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>; 
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 0w; EPOL := 0w; WL := 0w;
TRM := 0w; DPE0 := 0w; DPE1 := 1w; IS := 1w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>)` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def]);

(* (dr',spi') exists for init *)
val abs1_comb_hold_ref_rel_tau_comb_init = store_thm("abs1_comb_hold_ref_rel_tau_comb_init",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_init_start) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (ds_abs1 with state := abs1_ready) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (ds_abs1 with state := abs1_ready) (dr',spi')))``,
rw [] >> `IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
`(dr.state = dr_init_setting /\ spi.state = init_setregs) \/
(dr.state = dr_init_read_req /\ spi.state = init_setregs) \/
(dr.state = dr_init_check_rep /\ spi.state = init_setregs) \/
(dr.state = dr_init_read_req /\ spi.state = init_reset) \/
(dr.state = dr_init_check_rep /\ spi.state = init_reset) \/
(dr.state = dr_init_idle /\ spi.state = init_start) \/
(dr.state = dr_init_idle /\ spi.state = spi_ready)` by fs [IS_STATE_REL_def] >|[
(* dr_init_setting and init_setregs *)
`(dr.dr_init.issue_wr_sysconfig = spi.init.sysconfig_mode_done) /\
(dr.dr_init.issue_wr_modulctrl = spi.init.modulctrl_bus_done)`  
by fs [ref_rel_def] >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >> 
REVERSE (rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def]) >|[
(* ch0conf *)
DISJ1_TAC >>
rw [dr_write_ch0conf_init_def] >>
`spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`(19 >< 19) (66520w:word32):word1 <> spi.regs.CH0CONF.IS` 
by FULL_SIMP_TAC (std_ss++WORD_ss) [] >>
`ch0conf_changed (66520w:word32) spi` by fs [ch0conf_changed_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def, 
write_CH0CONF_comb_def, write_CH0CONF_init_def] >>
`7w:word5 >+ 2w:word5` by EVAL_TAC >>
fs [ref_rel_def, IS_STATE_REL_def],
(* modulctrl *)
DISJ2_TAC >>
`spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w /\ spi.regs.CH0CONF.WL = 0w` 
by fs [ref_rel_def] >>
`~dr.dr_init.issue_wr_modulctrl /\ dr.dr_init.issue_wr_sysconfig` by fs [ref_rel_def] >>
Q.EXISTS_TAC `SUC 0` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_init := dr.dr_init with issue_wr_modulctrl := T |>` >> 
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with <| 
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w |>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := spi.init with modulctrl_bus_done := T |>` >>
fs [n_tau_tr_dr_init_setting_1, ref_rel_def, IS_STATE_REL_def],
(* sysconfig_mode *)
DISJ2_TAC >>
`spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w /\ spi.regs.CH0CONF.WL = 0w` 
by fs [ref_rel_def] >>
`~dr.dr_init.issue_wr_modulctrl /\ ~dr.dr_init.issue_wr_sysconfig /\
~spi.init.modulctrl_bus_done` by fs [ref_rel_def] >>
Q.EXISTS_TAC `SUC 1` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T |> |>` >> 
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init :=  <|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>` >>
fs [n_tau_tr_dr_init_setting_2, ref_rel_def, IS_STATE_REL_def]],
(* dr_init_read_req and init_setregs *)
`spi.regs.SYSSTATUS = 1w /\ spi.regs.CH0CONF.WL = 0w /\
spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
`~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done` by fs [ref_rel_def] >>
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 3` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := 
<| issue_wr_sysconfig := T; issue_wr_modulctrl := T |> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init :=
<|sysconfig_mode_done := T; modulctrl_bus_done := T |> |>` >>
fs [n_tau_tr_dr_init_read_req_4, ref_rel_def, IS_STATE_REL_def],
(* dr_init_check_rep and init_set_regs *)
`~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done` by fs [ref_rel_def] >>
`dr.dr_last_read_ad = SOME SPI0_SYSSTATUS /\ ?v. dr.dr_last_read_v = SOME v` by fs [ref_rel_def] >>
`spi.regs.SYSSTATUS = 1w /\ spi.regs.CH0CONF.WL = 0w /\
spi.regs.CH0CONF.IS = 1w /\ spi.regs.CH0CONF.FORCE = 0w` by fs [ref_rel_def] >>
DISJ2_TAC >>
Cases_on `(0 >< 0) v:word1 = 1w` >-
((* the store value of sysstatus  is 1w *)
Q.EXISTS_TAC `SUC 2` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_check_rep_3, ref_rel_def, IS_STATE_REL_def]) >>
(* the store value of sysstatus is 0w *)
`(0 >< 0) v:word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 4` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <|issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := spi.regs.CH0CONF with
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_check_rep_5, ref_rel_def, IS_STATE_REL_def],
(* dr_init_read_req and init_reset *)
`~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done ` by fs [ref_rel_def] >>
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 4` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := 
<|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_read_req_5, ref_rel_def, IS_STATE_REL_def],
(* dr_init_check_rep and init_reset *)
`~ dr.dr_init.issue_wr_sysconfig /\ ~ dr.dr_init.issue_wr_modulctrl /\ 
~ spi.init.sysconfig_mode_done /\ ~ spi.init.modulctrl_bus_done` by fs [ref_rel_def] >>
`dr.dr_last_read_ad = SOME SPI0_SYSSTATUS /\ ?v. dr.dr_last_read_v = SOME v` by fs [ref_rel_def] >>
`(0 >< 0) v:word1 = 0w` by fs [ref_rel_def] >>
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 5` >>
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS;
dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with 
<| SYSCONFIG := spi.regs.SYSCONFIG with <|SIDLEMODE := 2w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w;
MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_check_rep_6, ref_rel_def, IS_STATE_REL_def],
(* dr_init_idle and init_start *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 5` >> 
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with <| SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w; MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_idle_6, ref_rel_def, IS_STATE_REL_def],
(* dr_init_idle and spi_ready *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 5` >> 
Q.EXISTS_TAC `dr with <| state := dr_ready; 
dr_last_read_ad := SOME SPI0_SYSSTATUS; dr_last_read_v := SOME 1w;
dr_init := <| issue_wr_sysconfig := T; issue_wr_modulctrl := T|> |>` >>
Q.EXISTS_TAC `spi with <|state := spi_ready;
regs := spi.regs with <| SYSCONFIG := <|SIDLEMODE := 2w; SOFTRESET := 0w; AUTOIDLE := 1w|>;
SYSSTATUS := 1w; MODULCTRL := <|SYSTEM_TEST := 0w; MS := 0w; SINGLE := 1w|>;
CH0CONF := <|PHA := 0w; POL := 0w; CLKD := 6w; EPOL := 1w; WL := 7w; 
TRM := 0w; DPE0 := 1w; DPE1 := 0w; IS := 0w; FORCE := 0w|> |>;
init := <|sysconfig_mode_done := T; modulctrl_bus_done := T|> |>` >>
fs [n_tau_tr_dr_init_idle_6, ref_rel_def, IS_STATE_REL_def]]);


(* related to tx automaton *)
(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_trans *)
val ref_rel_holds_tau_comb_abs1_tx_trans = store_thm("ref_rel_holds_tau_comb_abs1_tx_trans",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_trans) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length = dr.dr_tx.tx_cur_length` by fs [ref_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.tx_data_buf` by fs [ref_rel_def] >>
`(dr.state = dr_tx_write_data /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_read_txs /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_ready_for_trans)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_tx_write_data and tx_ready_for_trans *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def,
SPI0_CH0CTRL_def, write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_read_txs and tx_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_check_txs and tx_ready_for_trans *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_txs` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_tx_read_txs) = dr with <| state := dr_tx_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_trans_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_done_2 *)
val ref_rel_holds_tau_comb_abs1_tx_done_2 = store_thm("ref_rel_holds_tau_comb_abs1_tx_done_2",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_done_2) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def] >>
`ds_abs1.ds_abs1_tx.tx_cur_length = dr.dr_tx.tx_cur_length` by fs [ref_rel_def] >>
`ds_abs1.ds_abs1_tx.tx_data_buffer = dr.dr_tx.tx_data_buf` by fs [ref_rel_def] >>
`(dr.state = dr_tx_write_data /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_read_txs /\ spi.state = tx_trans_done) \/
(dr.state = dr_tx_check_txs /\ spi.state = tx_trans_done)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_tx_write_data and tx_trans_done *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_address_def, dr_write_value_def, dr_write_def,
dr_write_tx0_def] >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, 
SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_TX0_def,
SPI0_CH0CTRL_def, write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_read_txs and tx_trans_done *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_tx_check_txs and tx_trans_done *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_txs` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_tx_read_txs) = dr with <| state := dr_tx_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_tx_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [comb_abs1_tx_done_2_op_def, ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_tx_reset *)
val ref_rel_holds_tau_comb_abs1_tx_reset = store_thm("ref_rel_holds_tau_comb_abs1_tx_reset",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_tx_reset) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_tx_operations_def, comb_abs1_tx_reset_op_def] >>
`(dr.state = dr_tx_reset_conf /\ spi.state = tx_channel_disabled) \/
(dr.state = dr_tx_read_conf /\ spi.state = tx_channel_disabled) \/
(dr.state = dr_tx_issue_disable /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_read_eot /\ spi.state = tx_ready_for_trans) \/
(dr.state = dr_tx_check_eot /\ spi.state = tx_ready_for_trans)` by fs [IS_STATE_REL_def] >|
[(* dr_tx_reset_conf and tx_channel_disabled *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def, dr_write_state_def, 
dr_write_value_def,dr_write_address_def, dr_write_def, dr_write_ch0conf_tx_def] >>
`dr.dr_last_read_v = SOME (build_CH0CONF spi.regs.CH0CONF)` by fs [ref_rel_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) :word1 <> spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >> FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def,
write_CH0CONF_comb_def, write_CH0CONF_tx_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def, IS_STATE_REL_def],
(* dr_tx_read_conf and tx_channel_disabled *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 0:num` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <|state := dr_tx_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF spi = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF spi = spi)`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> 
fs [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) spi)` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_tx_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def,IS_STATE_REL_def],
(* dr_tx_issue_disable and tx_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`(dr_write_state dr = dr with state := dr_tx_read_conf) /\
(dr_write_address dr = SOME SPI0_CH0CTRL) /\
(dr_write_value dr = SOME (0w:word32))` 
by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def, 
dr_write_ch0ctrl_def] >> fs [] >>
`write_SPI_regs SPI0_CH0CTRL 0w spi = 
spi with <|regs := spi.regs with CH0CTRL := 0w;
state := tx_channel_disabled|>` 
by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
`dr_read (dr with state := dr_tx_read_conf) = dr with <|state := dr_tx_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>))`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
(spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w|>))` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_tx_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def,IS_STATE_REL_def],
(* dr_tx_read_eot and tx_ready_for_trans *)
DISJ2_TAC >>
`spi.regs.CH0STAT.EOT = 1w /\ spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >>
Q.EXISTS_TAC `SUC 3:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_tx_check_eot; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >> rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> rw [] >>
`dr_check (dr with <| state := dr_tx_check_eot; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |>) 
SPI0_CH0STAT (build_CH0STAT spi.regs.CH0STAT) = 
dr with <| state := dr_tx_issue_disable; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |> ` 
by (rw [dr_check_def, dr_check_tx_ch0stat_def,build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []) >> rw [] >>
`(dr_write_state (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = 
dr with <|state := dr_tx_read_conf;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) /\
(dr_write_address (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = SOME SPI0_CH0CTRL) /\
(dr_write_value (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = SOME (0w:word32))` 
by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def, 
dr_write_ch0ctrl_def] >> fs [] >>
`write_SPI_regs SPI0_CH0CTRL 0w spi = 
spi with <|regs := spi.regs with CH0CTRL := 0w;
state := tx_channel_disabled|>` 
by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
`dr_read (dr with <|state := dr_tx_read_conf;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = 
dr with <|state := dr_tx_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>` 
by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>))`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
(spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w|>))` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_tx_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def,IS_STATE_REL_def],
(* dr_tx_check_eot and tx_ready_for_trans *)
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
DISJ2_TAC >>
Cases_on `(2 >< 2) v:word1 = 1w /\ (1 >< 1) v:word1 = 1w` >|
[(* the stored values of txs and eot are 1w *)
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_issue_disable` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> rw [] >>
`(dr_write_state (dr with state := dr_tx_issue_disable) = dr with state := dr_tx_read_conf) /\
(dr_write_address (dr with state := dr_tx_issue_disable) = SOME SPI0_CH0CTRL) /\
(dr_write_value (dr with state := dr_tx_issue_disable) = SOME (0w:word32))` 
by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def, 
dr_write_ch0ctrl_def] >> fs [] >>
`write_SPI_regs SPI0_CH0CTRL 0w spi = 
spi with <|regs := spi.regs with CH0CTRL := 0w;
state := tx_channel_disabled|>` 
by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
`dr_read (dr with state := dr_tx_read_conf) = dr with <|state := dr_tx_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF |>` by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>))`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
(spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w|>))` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_tx_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def,IS_STATE_REL_def],
(* the stored values are not 1w *)
Q.EXISTS_TAC `SUC 4` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases, 
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_tx_read_eot` 
by rw [dr_check_def, dr_check_tx_ch0stat_def] >> rw [] >>
`spi.regs.CH0STAT.EOT = 1w /\ spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >>
`dr_read (dr with state := dr_tx_read_eot) = 
dr with <| state := dr_tx_check_eot; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >> rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> rw [] >>
`dr_check (dr with <| state := dr_tx_check_eot; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |>) 
SPI0_CH0STAT (build_CH0STAT spi.regs.CH0STAT) = 
dr with <| state := dr_tx_issue_disable; dr_last_read_ad := SOME SPI0_CH0STAT;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT) |> ` 
by (rw [dr_check_def, dr_check_tx_ch0stat_def,build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) []) >> rw [] >>
`(dr_write_state (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = 
dr with <|state := dr_tx_read_conf;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) /\
(dr_write_address (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = SOME SPI0_CH0CTRL) /\
(dr_write_value (dr with <|state := dr_tx_issue_disable;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = SOME (0w:word32))` 
by rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,dr_write_def, 
dr_write_ch0ctrl_def] >> fs [] >>
`write_SPI_regs SPI0_CH0CTRL 0w spi = 
spi with <|regs := spi.regs with CH0CTRL := 0w;
state := tx_channel_disabled|>` 
by rw [write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, 
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, write_CH0CTRL_def] >> fs [] >>
`dr_read (dr with <|state := dr_tx_read_conf;
dr_last_read_ad := SOME SPI0_CH0STAT; 
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>) = 
dr with <|state := dr_tx_reset_conf; 
dr_last_read_ad := SOME SPI0_CH0CONF;
dr_last_read_v := SOME (build_CH0STAT spi.regs.CH0STAT)|>` 
by rw [dr_read_def,dr_read_ch0conf_def] >> fs [] >>
`(read_SPI_regs_value SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = build_CH0CONF spi.regs.CH0CONF) /\
(read_SPI_regs_state SPI0_CH0CONF (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>) = (spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w |>))`
by fs [read_SPI_regs_value_def,read_SPI_regs_state_def,read_SPI_regs_def,
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,SPI0_SYSSTATUS_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >> fs [] >>
rw [dr_write_state_def,dr_write_address_def,dr_write_value_def,
dr_write_def, dr_write_ch0conf_tx_def] >>
`~ (ch0conf_changed ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) 
(spi with <|state := tx_channel_disabled;
regs := spi.regs with CH0CTRL := 0w|>))` 
by (fs [build_CH0CONF_def,ch0conf_changed_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
`spi.regs.CH0CONF.FORCE = 1w` by fs [ref_rel_def] >>
`(20 >< 20) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)) : word1 <> 
spi.regs.CH0CONF.FORCE` by FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
`(13 >< 12) ((4293918719w:word32) && (build_CH0CONF spi.regs.CH0CONF)): word2 = 
spi.regs.CH0CONF.TRM` by (fs [build_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) []) >>
rw [write_SPI_regs_def, write_CH0CONF_comb_def, write_CH0CONF_tx_def, 
SPI0_CH0CTRL_def, SPI0_PA_RANGE_def, SPI0_END_def, SPI0_START_def,
SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_BIT_EQ_ss) [] >>
fs [ref_rel_def,IS_STATE_REL_def]]]);

(* (dr', spi') exists for tx *)
val abs1_comb_hold_ref_rel_tau_comb_tx = store_thm("abs1_comb_hold_ref_rel_tau_comb_tx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_TX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_tx_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_TX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_tx_trans, ref_rel_holds_tau_comb_abs1_tx_done_2,
ref_rel_holds_tau_comb_abs1_tx_reset]);


(* related to rx automaton *)
(* ref_rel holds when ds_abs1 has tau_comb_transition and ds_abs1.state = abs1_rx_read *)
val ref_rel_holds_tau_comb_abs1_rx_read = store_thm("ref_rel_holds_tau_comb_abs1_rx_read",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_rx_read) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr', spi'))``,
rw [comb_abs1_rx_operations_def, comb_abs1_rx_read_op_def] >>
`dr.state = dr_rx_read_rx0 /\ spi.state = rx_data_ready` by fs [IS_STATE_REL_def] >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >>
rw [dr_read_def, dr_read_rx0_def, read_SPI_regs_value_def, read_SPI_regs_state_def,
read_SPI_regs_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def,
SPI0_CH0CTRL_def, SPI0_CH0STAT_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) []);

(* (ds',spi') exists for rx *)
val abs1_comb_hold_ref_rel_tau_comb_rx = store_thm("abs1_comb_hold_ref_rel_tau_comb_rx",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_RX_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_rx_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_RX_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_rx_read]);


(* related to xfer automaton *)
(* ref_rel holds when ds_abs1 has tau_comb transition and ds_abs1.state = abs1_xfer_prepare *)
val ref_rel_holds_tau_comb_abs1_xfer_prepare = store_thm("ref_rel_holds_tau_comb_abs1_xfer_prepare",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_prepare) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_prepare_op_def] >>
`(dr.state = dr_xfer_write_dataO /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_read_txs /\ spi.state = xfer_ready_for_trans) \/
(dr.state = dr_xfer_check_txs /\ spi.state = xfer_ready_for_trans)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.TXS = 1w` by fs [ref_rel_def] >|
[(* dr_xfer_write_dataO and xfer_ready_for_trans *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def,
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* dr_xfer_read_txs and xfer_ready_for_trans *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_xfer_check_txs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [],
(* dr_xfer_check_txs and xfer_ready_for_trans *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(1 >< 1) v:word1 = 1w` >|
[(* the stored value of txs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def,
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def,
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* the stored value of txs is 0w *)
`(1 >< 1) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_xfer_read_txs` 
by rw [dr_check_def, dr_check_xfer_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_xfer_read_txs) = dr with <| state := dr_xfer_check_txs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_write_state_def, dr_write_value_def, dr_write_address_def, dr_write_def,
dr_write_tx0_def, write_SPI_regs_def, SPI0_CH0CONF_def, SPI0_PA_RANGE_def, SPI0_TX0_def, 
SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_MODULCTRL_def, SPI0_CH0CTRL_def, 
write_TX0_def, CHECK_TXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);


(* ref_rel holds when ds_abs1 has tau_comb transition and ds_abs1.state = abs1_xfer_ready *)
val ref_rel_holds_tau_comb_abs1_xfer_ready = store_thm("ref_rel_holds_tau_comb_abs1_xfer_ready",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1.state = abs1_xfer_ready) /\
(IS_STATE_REL ds_abs1 dr spi) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [comb_abs1_xfer_operations_def, comb_abs1_xfer_ready_op_def] >>
`(dr.state = dr_xfer_read_rx0 /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_read_rxs /\ spi.state = xfer_data_ready) \/
(dr.state = dr_xfer_check_rxs /\ spi.state = xfer_data_ready)` by fs [IS_STATE_REL_def] >>
`spi.regs.CH0STAT.RXS = 1w` by fs [ref_rel_def] >|
[(* dr_xfer_read_rx0 and xfer_data_ready *)
DISJ1_TAC >>
rw [local_tr_cases, driver_tr_cases, spi_tr_cases, DR_TAU_ENABLE_def, 
SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) [],
(* dr_xfer_read_rxs and xfer_data_ready *)
DISJ2_TAC >>
Q.EXISTS_TAC `SUC 1:num` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
`dr_read dr = dr with <| state := dr_xfer_check_rxs;
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [],
(* dr_xfer_check_rxs and xfer_data_ready *)
DISJ2_TAC >>
`dr.dr_last_read_ad = SOME SPI0_CH0STAT /\ ?v. dr.dr_last_read_v =  SOME v` by fs [ref_rel_def] >>
Cases_on `(0 >< 0) v:word1 = 1w` >|
[(* the stored value of rxs is 1w *)
Q.EXISTS_TAC `SUC 0` >>
rw [n_tau_tr_def, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_RD_ENABLE_def, DR_WR_ENABLE_def, DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss ++ WORD_BIT_EQ_ss) [],
(* the stored value of rxs is 0w *)
`(0 >< 0) v: word1 = 0w` by rw [word1_not_1w_eq_0w] >>
Q.EXISTS_TAC `SUC 2` >>
rw [n_tau_tr_def, n_tau_tr_SUC, local_tr_cases, driver_tr_cases, spi_tr_cases,
DR_TAU_ENABLE_def, SPI_TAU_ENABLE_def, DR_WR_ENABLE_def, DR_RD_ENABLE_def] >>
`dr_check dr SPI0_CH0STAT v = dr with state := dr_xfer_read_rxs` 
by rw [dr_check_def, dr_check_xfer_ch0stat_def] >> 
rw [] >>
`dr_read (dr with state := dr_xfer_read_rxs) = dr with <| state := dr_xfer_check_rxs; 
dr_last_read_ad := SOME SPI0_CH0STAT |>` by rw [dr_read_def, dr_read_ch0stat_def] >>
rw [] >>
`read_SPI_regs_state SPI0_CH0STAT spi = spi /\
read_SPI_regs_value SPI0_CH0STAT spi = build_CH0STAT spi.regs.CH0STAT` by
rw [read_SPI_regs_state_def, read_SPI_regs_value_def, read_SPI_regs_def, SPI0_CH0STAT_def,
SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def, SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def,
SPI0_MODULCTRL_def, SPI0_CH0CONF_def] >>
rw [dr_check_def, dr_check_xfer_ch0stat_def, build_CH0STAT_def] >>
FULL_SIMP_TAC (std_ss++WORD_ss++WORD_EXTRACT_ss) [] >>
rw [dr_read_def, read_SPI_regs_value_def, read_SPI_regs_state_def, read_SPI_regs_def,
dr_read_rx0_def, SPI0_RX0_def, SPI0_PA_RANGE_def, SPI0_START_def, SPI0_END_def,
SPI0_SYSCONFIG_def, SPI0_SYSSTATUS_def, SPI0_MODULCTRL_def, SPI0_CH0CONF_def, 
SPI0_CH0STAT_def, SPI0_CH0CTRL_def, SPI0_TX0_def, read_RX0_def, CHECK_RXS_BIT_def] >>
fs [ref_rel_def, IS_STATE_REL_def, SPI0_RX0_def] >>
SIMP_TAC (std_ss++WORD_BIT_EQ_ss) []]]);

(* (dr',spi') exists for xfer *)
val abs1_comb_hold_ref_rel_tau_comb_xfer = store_thm("abs1_comb_hold_ref_rel_tau_comb_xfer",
``!spi dr ds_abs1.
(ref_rel ds_abs1 (dr, spi)) /\ (COMB_ABS1_XFER_ENABLE ds_abs1) ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ 
(ref_rel (comb_abs1_xfer_operations ds_abs1) (dr',spi')))``,
rw [COMB_ABS1_XFER_ENABLE_def] >>
`IS_STATE_REL ds_abs1 dr spi` by fs [ref_rel_def] >>
rw [ref_rel_holds_tau_comb_abs1_xfer_prepare, ref_rel_holds_tau_comb_abs1_xfer_ready]);

(* simulation: (dr',spi') exists and holds the ref_rel when ds_abs1 has tau_comb transitions *)
val abs1_comb_hold_ref_rel_tau_comb = store_thm("abs1_comb_hold_ref_rel_tau_comb",
``!spi dr ds_abs1 ds_abs1'.
(ref_rel ds_abs1 (dr, spi)) /\ (ds_abs1_comb_tr ds_abs1 tau_comb ds_abs1') ==>
(?dr' spi'. (local_tr (dr, spi) tau (dr', spi')) /\ (ref_rel ds_abs1' (dr', spi'))) \/
(?n dr' spi'. (n_tau_tr n local_tr (dr,spi) tau (dr',spi')) /\ (ref_rel ds_abs1' (dr',spi')))``,
rw [ds_abs1_comb_tr_cases, COMB_ABS1_INIT_ENABLE_def, 
comb_abs1_init_operations_def, comb_abs1_init_start_op_def] >>
rw [abs1_comb_hold_ref_rel_tau_comb_init, abs1_comb_hold_ref_rel_tau_comb_tx,
abs1_comb_hold_ref_rel_tau_comb_rx, abs1_comb_hold_ref_rel_tau_comb_xfer]);

val _ = export_theory();
