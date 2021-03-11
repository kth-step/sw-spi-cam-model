open HolKernel bossLib boolLib Parse wordsLib;
open cam_stateTheory cam_memTheory ds_abs0_xferTheory;

val _ = new_theory "cam_RD_RE";

(* return one byte data from the data register *)
val cam_return_data_def = Define `
cam_return_data (cam:cam_state) =
if cam.state = cam_capture_done then
cam with <|state := cam_start;
d1 := call_xfer_ds_abs0 cam.d1 [cam.regs.CAM_DATA] |>
else cam with err := T`

(* return the camera register value *)
val cam_return_regs_def = Define `
cam_return_regs (cam:cam_state) (ad:word8) =
if ad = CAM_CTRL_PA then 
cam with d1 := call_xfer_ds_abs0 cam.d1 [w2w cam.regs.CAM_CTRL]
else if ad = CAM_TRIG_PA then 
cam with d1 := call_xfer_ds_abs0 cam.d1 [w2w cam.regs.CAM_TRIG]
else if ad = CAM_DATA_PA then cam_return_data cam
(* address are not included *)
else cam`


val _ = export_theory ();
