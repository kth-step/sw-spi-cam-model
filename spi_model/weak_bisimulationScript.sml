open HolKernel bossLib boolLib Parse;
open SPI_stateTheory;

val _ = new_theory "weak_bisimulation";

(* a state can be reached after n tau steps *)
val n_tau_tr_def = Define `
(n_tau_tr (0:num) (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = (tr s lbl s')) /\
(n_tau_tr (n:num) (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = 
?(s'':'a). (tr s tau s'') /\ (n_tau_tr (n-1) tr s'' lbl s'))`

val n_tau_tr_SUC = store_thm("n_tau_tr_SUC",
``!tr s s' n lbl. (n > 0) ==> 
n_tau_tr n tr s lbl s' = n_tau_tr (SUC (n - 1)) tr s lbl s'``, 
rw [] >>
`n = SUC (n - 1)` by  fs[] >>
METIS_TAC[]);

(* define the weak transition relation *)
val weak_tr_def = Define `
weak_tr (tr:'a -> global_lbl_type -> 'a -> bool) (s:'a) (lbl:global_lbl_type) (s':'a) = 
((tr s lbl s') \/
(s = s' /\ lbl = tau) \/
(?n. n_tau_tr n tr s lbl s'))`

(* define the weak bisimulation realtion *)
val weak_bisim_def = Define `
weak_bisim (r:'a -> 'b -> bool) (tr1:'a -> global_lbl_type -> 'a -> bool) (tr2:'b -> global_lbl_type -> 'b -> bool) =
(!s1 s2. r s1 s2 ==>
(!lbl s1'. tr1 s1 lbl s1' ==> ?s2'. weak_tr tr2 s2 lbl s2' /\ r s1' s2') /\
(!lbl s2'. tr2 s2 lbl s2' ==> ?s1'. weak_tr tr1 s1 lbl s1' /\ r s1' s2'))`


val _ = export_theory();
