open HolKernel bossLib boolLib Parse wordsLib;
open cam_stateTheory cam_WR_UPTheory xfer_correctTheory cam_memTheory;

val _ = new_theory "cam_cmds_thm"

(* camera model can receive the data from the main device. *)
val cam_rec_capture_cmd = store_thm("cam_rec_capture_cmd",
``!cam d0 d0' d1'.
cam.d1.state = abs0_ready /\ d0.state = abs0_ready ==>
ds_abs0_tr d0 (call_xfer [0x84w; 0x01w]) d0' /\
ds_abs0_tr cam.d1 (call_xfer [0x00w; 0x00w]) d1' ==>
?n d0'' d1''. n_tau_tr n abs0_global_tr (d0',d1') tau (d0'',d1'') /\
d0''.ds_abs0_xfer.xfer_dataIN_buffer = [0x00w;0x00w] /\
d1''.ds_abs0_xfer.xfer_dataIN_buffer = [0x84w;0x01w]``,
rw [] >>
`LENGTH [0x84w:word8;0x01w:word8] = LENGTH [0x00w:word8;0x00w:word8]` by rw [] >>
`[0x84w:word8;0x01w:word8] <> [] /\ [0x00w:word8;0x00w:word8] <> []` by rw [] >>
METIS_TAC [abs0_xfer_correct]);

(* With correct command, capture can start capture. *)
val cam_capture_correct = store_thm("cam_capture_correct",
``!cam cam'.
cam.d1.ds_abs0_xfer.xfer_dataIN_buffer = [0x84w;0x01w] ==>
cam.state = cam_start ==>
cam' = cam_update_regs cam 0x84w 0x01w ==>
cam'.state = cam_capturing``,
rw [cam_update_regs_def, CAM_CTRL_PA_def, cam_update_ctrl_def]);



val _ = export_theory ();
