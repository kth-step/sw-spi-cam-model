open HolKernel bossLib boolLib Parse wordsLib;
open cam_stateTheory cam_memTheory;

val _ = new_theory "cam_WR_UP";

(* update the CAM_CTRL register, to start capture *)
val cam_update_ctrl_def = Define `
cam_update_ctrl (cam:cam_state) (v:word1) =
if cam.state = cam_start /\ v = 1w then
cam with <|state := cam_capturing;
regs := cam.regs with CAM_CTRL := 1w|>
else if cam.state = cam_start then (* v = 0w *) cam
else cam with err := T (* wrong state *)`

(* update the camera register *)
val cam_update_regs_def = Define `
cam_update_regs (cam:cam_state) (ad:word8) (v:word8) =
let ad1 = (6 >< 0) ad:word8 and
    v1 = (0 >< 0) v:word1 in
if ad1 = CAM_CTRL_PA then cam_update_ctrl cam v1
(* TRIG and DATA regs are read-only *)
else cam`


val _ = export_theory ();
