From stdpp Require Import gmap sorting.

(* [gset K] is the type of sets you probably want to use. It enjoys good
properties w.r.t. computation (most operations are logarithmic or linear) and
equality. It works for any type [K] that is countable (see type class
[Countable]). There are [Countable] instances for all the usual types, [nat],
[list nat], [nat * nat], [gset nat], etc. *)

Check gset.

(* All the set operations are overloaded via type classes, but there are
instances for [gset]. The most important operations are:

- [elem_of], notation [∈]
- [subseteq], notation [⊆]
- [subset], notation [⊂]
- [empty], notation [∅]
- [singleton], notation [ {[ x ]} ]
- [union], notation [∪]
- [intersection], notation [∩]
- [difference], notation [∖]
*)

(* Let us try to type check some stuff. *)

Check {[ 10 ]} : gset nat.

Check {[ [10] ]} : gset (list nat).

Check {[ {[ 10 ]} ]} : gset (gset nat).

Check (λ X : gset nat, X ∪ {[ 10 ]}).

(** And let us write some lemmas. The most useful tactic is [set_solver]. *)

Lemma some_stuff (X Y Z : gset nat) :
  X ∪ Y ∩ X ∪ Z ∩ X = (Y ∪ X ∪ Z ∖ ∅ ∪ X) ∩ X.
Proof. set_solver. Qed.

Lemma some_stuff_poly `{Countable A} (X Y Z : gset A) :
  X ∪ Y ∩ X ∪ Z ∩ X = (Y ∪ X ∪ Z ∖ ∅ ∪ X) ∩ X.
Proof. set_solver. Qed.

(** If you want to search for lemmas, search for the operations (using their typeclass names), not [gset]
since all lemmas are overloaded. *)

Search difference intersection.

(** Some important notes:

- The lemmas look a bit daunting because of the additional arguments due to
  type classes, but these arguments can mostly be ignored
- There are both lemmas about Leibniz equality [=] and setoid equality [≡].
  The first ones are suffixed [_L]. For [gset] you always want to use [=] (and
  thus the [_L] lemmas) because we have [X ≡ Y ↔ X = Y]. This is not the case
  for other implementations of sets, like [propset A := A → Prop] or
  [listset A := list A], hence [≡] is useful in the general case. *)

(** Some other examples *)

Definition evens (X : gset nat) : gset nat :=
  filter (λ x, (2 | x)) X.
Definition intersection_alt (X Y : gset nat) : gset nat :=
  filter (.∈ Y) X.
Definition add_one (X : gset nat) : gset nat :=
  set_map S X.
Definition until_n (n : nat) : gset nat :=
  set_seq 0 n.

(** Keep in mind that [filter], [set_map], [set_seq], etc are overloaded via
type classes. So, you need sufficient type information in your definitions and
you won't find much about them when searching for [gset]. *)

(** When computing with sets, always make sure to cast the result that you want
to display is a simple type like [nat], [list nat], [bool], etc. The result
of a [gset] computation is a big sigma type with lots of noise, so it won't be
pretty (or useful) to look at. *)

Eval vm_compute in (elements (add_one (evens {[ 10; 11; 14 ]}))).
Eval vm_compute in (elements (evens (until_n 40))).
(** [elements] converts a set to a list. They are not sorted, but you can do
that yourself. *)
Eval vm_compute in (merge_sort (≤) (elements (evens (until_n 40)))).
Eval vm_compute in (fresh ({[ 10; 12 ]} : gset nat)).
Eval vm_compute in (size ({[ 10; 12 ]} : gset nat)).
(** You can use [bool_decide] to turn decidable [Prop]s into [bool]s. *)
Eval vm_compute in bool_decide (10 ∈ evens {[ 10; 11 ]}).
Eval vm_compute in (bool_decide ({[ 10; 14; 17 ]} ⊂ until_n 40)).
Eval vm_compute in (bool_decide (set_Forall (λ x, (2 | x)) (evens (until_n 40)))).

(** Want to know more?

- Look up the definitions of the type classes for [union], [intersection], etc.,
  interfaces [SimpleSet], [Set_], etc. in [theories/base.v].
- Look up the generic theory of sets in [theories/sets.v].
- Look up the generic theory of finite sets in [theories/fin_sets.v].
- Probably don't look into the implementation of [gset] in [theories/gmap.v],
  unless you are very interested in encodings as bit strings and radix-2 search
  trees. You should treat [gset] as a black box. *)
