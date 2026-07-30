From stdpp Require Import tactics telescopes strings vector.

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

Section dependent_accessor.
  (** This is a dependent variant of [accessor] above. The differces are:
  [Y] is a function from values of [X] to telescopes, hence types in [Y] can
  depend on elements of the telescope [X]. [β] and [γ] are hence dependent
  Rocq functions. *)
  Definition dep_accessor {X : tele} {Y : X → tele}
      (α : X → Prop) (β Φ : ∀ x : X, Y x → Prop) : Prop :=
    ∃.. x, α x ∧ (∀.. y, β x y → Φ x y).
  
  (* The same notation as for [accessor] above but for [dep_accessor].*)
  Section notation_tests.
    Notation "'AACC' '<{' ∃∃ x1 .. xn , α '}>' '<{' ∀∀ y1 .. yn , β , 'COMM' γ '}>'" :=
      (dep_accessor
        (X:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
        (* In [dep_accessor], [Y] is a function on [X] and hence handled
        similarly to [α] in the non-dependent notation. *)
        (Y:=tele_app $ λ x1, .. (λ xn, TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. )) .. )
        (tele_app $ λ x1, .. (λ xn, α) ..)
        (* For [β] and [Φ] the outer [tele_app] is applied to a dependent
        telescopic function of type [tele_fun X (λ x, Y x → Prop)], as the
        inner telescope [Y] is dependent on [X]. *)
        (tele_app $ λ x1, .. (λ xn,
            tele_app $ λ y1, .. (λ yn, β) ..
          ) .. )
        (tele_app $ λ x1, .. (λ xn,
            tele_app $ λ y1, .. (λ yn, γ) .. 
          ) .. )
      )
      (at level 0, α, β, γ at level 200, x1 binder, xn binder, y1 binder, yn binder).

    Check "dep_aacc_notation_test".
    (** Using a vector we can express the AACC from [aacc_notation_test] more
    nicely. In the second telescope, we use a vector whose length depends on the
    number [n] in the first telescope. In this test we show unfolding the notation
    still gives simple existentials and foralls, and that the AACC using vectors
    is equivalent to the non-dependent version using lists. *)
    Lemma aacc_notation_test (α : nat → Prop) (β Φ : nat → list nat → Prop) :
      AACC <{ ∃∃ (n : nat), α n }>
           <{ ∀∀ (v : vec nat n), β n v, COMM Φ n v }> ↔
      AACC <{ ∃∃ (n : nat), α n }>
           <{ ∀∀ (l : list nat), n = length l ∧ β n l, COMM Φ n l }>.
    Proof.
      Show.
      unfold dep_accessor. simpl in *.
      Show.
      split.
      - intros (x & Hα & Hcomm).
        exists x. split; first done.
        intros l [-> Hβ].
        rewrite <-vec_to_list_to_vec.
        eapply Hcomm.
        by rewrite vec_to_list_to_vec.
      - intros (x & Hα & Hcomm).
        exists x. split; first done.
        intros l Hβ.
        eapply Hcomm.
        by rewrite length_vec_to_list.
    Qed.
  End notation_tests.

  (** Some example lemmas about abstract dependent telescopes. The lemmas and
  proofs are the same as for [accessor], but the telescope [Y] is dependent on
  [X]. *)
  Section abstract_tests.
    Context {X : tele} {Y : X → tele}.
    Implicit Types α : X → Prop.
    Implicit Types β Φ : ∀ x : X, Y x → Prop.

    Lemma dep_aacc_mono α β Φ1 Φ2 :
      (∀.. x y, Φ1 x y → Φ2 x y) →
      dep_accessor α β Φ1 → dep_accessor α β Φ2.
    Proof.
      unfold dep_accessor. rewrite !tforall_forall, !texist_exist.
      intros HΦ12 Hacc. destruct Hacc as [x' [Hα Hclose]]. exists x'.
      specialize (HΦ12 x').
      split; [done|].
      rewrite !tforall_forall in *.
      intros y' Hβ.
      apply HΦ12, Hclose. done.
    Qed.

    Check "dep_aacc_mono_disj".
    Lemma dep_aacc_mono_disj α β Φ1 Φ2 :
      dep_accessor α β Φ1 → dep_accessor α β (λ.. x y, Φ1 x y ∨ Φ2 x y).
    Proof.
      Show.
      apply dep_aacc_mono. Show.
      rewrite !tforall_forall. intros x.
      rewrite !tforall_forall. intros y HΦ1.
      rewrite !tele_app_bind. Show.
      left. done.
    Qed.
  End abstract_tests.
End dependent_accessor.
