open HolKernel bossLib boolLib Parse wordsLib;
open cam_stateTheory cam_WR_UPTheory cam_RD_RETheory xfer_correctTheory cam_memTheory;

val _ = new_theory "cam_cmds_thm"

(* camera can receive the command to update the CTRL register through ds_abs0. *)
val cam_rec_capture_cmd = store_thm("cam_rec_capture_cmd",
``!cam d0 d0' d1' a1 a2.
cam.d1.state = abs0_ready /\ d0.state = abs0_ready ==>
ds_abs0_tr d0 (call_xfer [0x84w; 0x01w]) d0' /\
ds_abs0_tr cam.d1 (call_xfer [a1; a2]) d1' ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = [0x84w;0x01w]``,
rw [] >>
`LENGTH [0x84w:word8;0x01w:word8] = LENGTH [a1;a2]` by rw [] >>
`[0x84w:word8;0x01w:word8] <> [] /\ [a1;a2] <> []` by rw [] >>
METIS_TAC [abs0_xfer_correct]);

(* With correct command, capture can start capture. *)
val cam_capture_correct = store_thm("cam_capture_correct",
``!cam cam'.
cam.d1.ds_abs0_xfer.xfer_dataIN_buffer = [0x84w;0x01w] ==>
cam.state = cam_start ==>
cam' = cam_update_regs cam 0x84w 0x01w ==>
cam'.state = cam_capturing``,
rw [cam_update_regs_def, CAM_CTRL_PA_def, cam_update_ctrl_def]);

(* Camera can receive the read commands *)
val cam_rec_read_cmds = store_thm("cam_rec_read_cmds",
``!cam d0 d0' d1' ad a.
cam.d1.state = abs0_ready /\ d0.state = abs0_ready ==>
ad = CAM_CTRL_PA \/ ad = CAM_TRIG_PA \/ ad = CAM_DATA_PA ==>
ds_abs0_tr d0 (call_xfer [ad]) d0' /\
ds_abs0_tr cam.d1 (call_xfer [a]) d1' ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = [ad]``,
rw [] >>
`LENGTH [CAM_CTRL_PA] = LENGTH [a] /\
 LENGTH [CAM_TRIG_PA] = LENGTH [a] /\
 LENGTH [CAM_DATA_PA] = LENGTH [a]` by rw [] >>
`[CAM_CTRL_PA] <> [] /\ [CAM_TRIG_PA] <> [] /\ [CAM_DATA_PA] <> [] /\ [a] <> []` by rw [] >>
METIS_TAC [abs0_xfer_correct]);

(* Camera will return corresponding register value *)
(* CAM_CTRL *)
val cam_prepare_ctrl_value = store_thm("cam_prepare_ctrl_value",
``!cam cam'.
cam.d1.ds_abs0_xfer.xfer_dataIN_buffer = [CAM_CTRL_PA] ==>
cam' = cam_return_regs cam CAM_CTRL_PA ==>
cam'.d1 = call_xfer_ds_abs0 cam.d1 [w2w cam.regs.CAM_CTRL]``,
rw [cam_return_regs_def]);

(* CAM_TRIG *)
val cam_prepare_trig_value = store_thm("cam_prepare_trig_value",
``!cam cam'.
cam.d1.ds_abs0_xfer.xfer_dataIN_buffer = [CAM_TRIG_PA] ==>
cam' = cam_return_regs cam CAM_TRIG_PA ==>
cam'.d1 = call_xfer_ds_abs0 cam.d1 [w2w cam.regs.CAM_TRIG]``,
rw [cam_return_regs_def, CAM_TRIG_PA_def, CAM_CTRL_PA_def]);

(* CAM_DATA *)
val cam_prepare_data_value = store_thm("cam_prepare_data_value",
``!cam cam'.
cam.d1.ds_abs0_xfer.xfer_dataIN_buffer = [CAM_DATA_PA] ==>
cam.state = cam_capture_done ==>
cam' = cam_return_regs cam CAM_DATA_PA ==>
cam'.d1 = call_xfer_ds_abs0 cam.d1 [cam.regs.CAM_DATA]``,
rw [cam_return_regs_def, CAM_TRIG_PA_def, CAM_CTRL_PA_def, CAM_DATA_PA_def,
cam_return_data_def]);

(* camera can send back the register vaule, the main device can receive it. *)
val cam_rec_read_cmds = store_thm("cam_rec_read_cmds",
``!cam d0 d0' d1' v a.
cam.d1.state = abs0_ready /\ d0.state = abs0_ready ==>
ds_abs0_tr d0 (call_xfer [a]) d0' /\
ds_abs0_tr cam.d1 (call_xfer [v]) d1' ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = [v]``,
rw [] >>
`LENGTH [v] = LENGTH [a]` by rw [] >>
`[v] <> [] /\ [a] <> []` by rw [] >>
METIS_TAC [abs0_xfer_correct]);

val _ = export_theory ();
