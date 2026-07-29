From stdpp Require Import tactics telescopes strings.

Local Unset Mangle Names. (* for stable goal printing *)

Section universes.
  (** This test would fail without [Unset Universe Minimization ToSet] in
  [telescopes.v]. *)
  Lemma texist_exist_universes (X : Type) (P : TeleS (λ _ : X, TeleO) → Prop) :
    texist P ↔ ex P.
  Proof. by rewrite texist_exist. Qed.

  (** [tele_arg t] should live at the same universe as the types inside of [t]
  because [tele_arg t] is essentially just a (dependent) product. *)
  Definition no_bump@{u} (t : tele@{u}) : Type@{u} := tele_arg@{u} t.

  (** Assert that telescopes are cumulatively universe polymorphic.
  See https://gitlab.mpi-sws.org/iris/iris/-/issues/461 *)
  Section cumulativity.
    Monomorphic Universes Quant local.
    Monomorphic Constraint local < Quant.
    Example cumul (t : tele@{local}) : tele@{Quant} := t.
  End cumulativity.
End universes.

(** Type inference for [tele_app]-based notation. (Relies on [&]
bidirectionality hint of [tele_app].) *)
Definition test {TT : tele} (t : TT → Prop) : Prop :=
  ∀.. x, t x ∧ t x.
Notation "'[TEST'  x .. z ,  P ']'" :=
  (test (TT:=(TeleS (λ x, .. (TeleS (λ z, TeleO)) ..)))
        (tele_app (λ x, .. (λ z, P) ..)))
  (x binder, z binder).
Check [TEST (x y : nat), x = y].

(** [tele_arg ..] notation tests.
These tests mainly test type annotations and casts in the [tele_arg] notations.
We test that Rocq can typecheck literal telescope arguments in two ways:
- tactic unification/old unification using [exact]
- evarconv/new unification using [refine] *)
Example tele_arg_notation_0 : [tele].
Proof.
  assert_succeeds exact [tele_arg].
  assert_succeeds refine [tele_arg].
Abort.

Example tele_arg_notation_1 : [tele (_:nat)].
Proof.
  assert_succeeds exact [tele_arg 0].
  assert_succeeds refine [tele_arg 0].
Abort.

Example tele_arg_notation_2 : [tele (_ : bool) (_ : nat)].
Proof.
  assert_succeeds exact [tele_arg true; 0].
  assert_succeeds refine [tele_arg true; 0].
Abort.

Example tele_arg_notation_2_dep : [tele (b : bool) (_ : if b then nat else False)].
Proof.
  assert_succeeds exact [tele_arg true; 0].
  assert_succeeds refine [tele_arg true; 0].
Abort.

Section accessor.
  (** This is like Iris's atomic accessors (see [iris:iris.bi.lib.atomic]), but
  in [Prop] and without ABORT. Just to play with telescopes. *)
  Definition accessor {X Y : tele} (α : X → Prop) (β Φ : X → Y → Prop) : Prop :=
    ∃.. x, α x ∧ (∀.. y, β x y → Φ x y).

  (** The notation from Iris, but again in [Prop] and without ABORT. *)
  Section notations.
    Notation "'AACC' '<{' ∃∃ x1 .. xn , α '}>' '<{' ∀∀ y1 .. yn , β , 'COMM' γ '}>'" :=
      (accessor
        (X:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
        (Y:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
        (tele_app $ λ x1, .. (λ xn, α) ..)
        (tele_app $ λ x1, .. (λ xn,
            tele_app $ λ y1, .. (λ yn, β) ..
          ) .. )
        (tele_app $ λ x1, .. (λ xn,
            tele_app $ λ y1, .. (λ yn, γ) .. 
          ) .. )
      )
      (at level 0, α, β, γ at level 200, x1 binder, xn binder, y1 binder, yn binder).

    Check "aacc_notation_test".
    Lemma aacc_notation_test (α : nat → Prop) (β Φ : nat → list nat → Prop) :
      AACC <{ ∃∃ (n : nat), α n }>
           <{ ∀∀ (l : list nat), n = length l ∧ β n l, COMM Φ n l }>.
    Proof.
      Show.
      (** Test that if we [unfold] the definition of [accessor], and we [simpl] we
      indeed get iterated [∀] and [∃] quantifiers instead of [∀..] and [∃..]. *)
      unfold accessor. simpl in *.
      Show.
    Abort.
  End notations.

  (** Some example lemmas about abstract telescopes. *)
  Section tests.
    Context {X : tele} {Y : tele}.
    Implicit Types (α : X → Prop) (β Φ : X → Y → Prop).

    (** In Iris, we do not have to rewrite with [tforall_forall] and [texist_exist]
    by hand, that is done automatically by the proof mode when using [iIntros],
    [iApply], etc. *)
    Lemma acc_mono α β Φ1 Φ2 :
      (∀.. x y, Φ1 x y → Φ2 x y) →
      accessor α β Φ1 → accessor α β Φ2.
    Proof.
      unfold accessor. rewrite tforall_forall, !texist_exist.
      intros HΦ Hacc. destruct Hacc as (x & Hα & Hclose).
      specialize (HΦ x). rewrite tforall_forall in HΦ.
      exists x. split; [done|].
      revert Hclose. rewrite !tforall_forall.
      intros Hclose y Hβ. apply HΦ, Hclose. done.
    Qed.

    Lemma acc_mono_disj α β Φ1 Φ2 :
      accessor α β Φ1 → accessor α β (λ.. x y, Φ1 x y ∨ Φ2 x y).
    Proof.
      Show.
      apply acc_mono. Show.
      apply tforall_forall; intros x. apply tforall_forall; intros y Hclose.
      rewrite !tele_app_bind. Show.
      left. done.
    Qed.
  End tests.
End accessor.
