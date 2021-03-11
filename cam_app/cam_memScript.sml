open HolKernel bossLib boolLib Parse wordsLib;

val _ = new_theory "cam_mem";

(* Physical address of camera control register *)
val CAM_CTRL_PA_def = Define `CAM_CTRL_PA = 0x04w:word8`

(* Physical address of camera trigger register *)
val CAM_TRIG_PA_def = Define `CAM_TRIG_PA = 0x41w:word8`

(* Physical address of camera data register *)
val CAM_DATA_PA_def = Define `CAM_DATA_PA = 0x3Dw:word8`

val _ = export_theory ();
