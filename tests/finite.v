From Stdlib Require Import String.
From stdpp Require Import finite fin sets.

Local Open Scope string_scope.

Check "enum_simpl_never_and_set_solver".
Lemma enum_simpl_never_and_set_solver {n} (i : fin n) :
  i ∈ enum (fin n).
Proof.
  (* Check that [simpl] doesn't unfold [enum]. *)
  simpl.
Show.
  apply elem_of_enum.
Restart. Proof.
  set_solver.
Qed.
