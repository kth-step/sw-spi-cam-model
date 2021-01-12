open HolKernel bossLib boolLib Parse;
open wordsLib wordsTheory;
open abs_invTheory;

val _ = new_theory "spi_abs_preserves_inv"














(* fianl goal for invariant proof *)
val spi_abs_preserves_invariant = store_thm("spi_abs_preserves_invariant",
``!spi_abs l. (spi_abs_invariant spi_abs) /\ (spi_abs_tr spi_abs l spi_abs') 
==> (spi_abs_invariant spi_abs')``,
cheat);



val _ = new_theory();
