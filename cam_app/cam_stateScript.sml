open HolKernel bossLib boolLib Parse;
open ds_abs0_stateTheory;

val _ = new_theory "cam_state";

(* camear device, an example *)
(* camera general state *)
val _ = Datatype `cam_general_state =
| cam_start | cam_capturing | cam_capture_done`

(* camera registers *)
val _ = Datatype `cam_regs = <|
CAM_CTRL: word1; (* control register *)
CAM_TRIG: word1; (* trigger register *)
CAM_DATA: word8  (* data register *)|>`

(* camera state *)
val _ = Datatype `cam_state = <|
err: bool;
state: cam_general_state;
regs: cam_regs;
d1: ds_abs0_state |>`

(* main device: control the camera through ds_abs0 interface 
(* main device general state *)
val _ = Datatype `main_general_state =
| main_start | main_read | main_check | main_fetch` 

(* main device state *)
val _ = Datatype `main_state = <|
err: bool;
state: main_general_state;
d0: ds_abs0_state |>`
*)

val _ = export_theory (); 
