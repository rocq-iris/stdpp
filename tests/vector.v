From stdpp Require Import vector.

Section test.
  Context {A : Type} {n : nat}.
  Implicit Types (v : vec A n) (i : fin n).

  (* Test coercions interaction between [insert] and [vec_to_list] work as expected.
  The instance [vector_insert] should take priority, so [<[_:=_]> v] on a [vec] [v] 
  should always result in a [vec], not a list. We check this by re-stating the 
  [insert] lemmas with coercions implicit, and trying to apply the original. *)

  Lemma vec_to_list_insert_again v i x :
    (<[i:=x]> v : list _) = <[i : nat:=x]> (v : list _).
  Proof. rewrite vec_to_list_insert. reflexivity. Qed.
  Lemma vec_to_list_insert_again_reverse v i x :
    <[i : nat :=x]> (v : list _) = <[i:=x]> v.
  Proof. rewrite vec_to_list_insert. reflexivity. Qed.

  (* test version without coercion *)
  Lemma Forall_vinsert_again (P : A → Prop) v i x :
    Forall P v →
    P x →
    Forall P (<[i:=x]> v).
  Proof. apply Forall_vinsert. Qed. 
End test.
