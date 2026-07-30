From stdpp Require Import base tactics.

Local Set Universe Polymorphism.
Local Set Polymorphic Inductive Cumulativity.

(** Without this flag, Rocq minimizes some universes to [Set] when they
    should not be, e.g. in [texist_exist].
    See the [texist_exist_universes] test. *)
Local Unset Universe Minimization ToSet.

(** Telescopes *)
Inductive tele : Type :=
  | TeleO : tele
  | TeleS {X} (binder : X → tele) : tele.

Global Arguments TeleS {_} _.

(** A duplication of the type [sigT] to avoid any connection to other universes.
 *)
Record tele_arg_cons {X : Type} (f : X → Type) : Type := TeleArgCons
  { tele_arg_head : X;
    tele_arg_tail : f tele_arg_head }.
Global Arguments TeleArgCons {_ _} _ _.

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Fixpoint tele_arg@{u} (t : tele@{u}) : Type@{u} :=
  match t with
  | TeleO => unit
  | TeleS f => tele_arg_cons (λ x, tele_arg (f x))
  end.
Global Arguments tele_arg _ : simpl never.

(* Rocq has no idea that [unit] and [tele_arg_cons] have anything to do with
   telescopes. This only becomes a problem when concrete telescope arguments
   (of concrete telescopes) need to be typechecked. To work around this, we
   annotate the notations below with extra information to guide unification.
 *)

(* The cast in the notation below is necessary to make Rocq understand that
   [TargO] can be unified with [tele_arg TeleO]. *)
Notation TargO := (tt : tele_arg TeleO) (only parsing).
(* The casts and annotations are necessary for Rocq to typecheck nested [TargS]
   as well as the final [TargO] in a chain of [TargS]. *)
Notation TargS a b :=
  ((@TeleArgCons _ (λ x, tele_arg (_ x)) a b) : (tele_arg (TeleS _))) (only parsing).
Coercion tele_arg : tele >-> Sortclass.

Lemma tele_arg_ind (P : ∀ TT, tele_arg TT → Prop) :
  P TeleO TargO →
  (∀ T (b : T → tele) x xs, P (b x) xs → P (TeleS b) (TargS x xs)) →
  ∀ TT (xs : tele_arg TT), P TT xs.
Proof.
  intros H0 HS TT. induction TT as [|T b IH]; simpl.
  - by intros [].
  - intros [x xs]. by apply HS.
Qed.

(** The telescope version of Rocq's dependent function type. The iterated dependent
  Rocq function [∀ (x1 : A1) .. (xn : An), B x1 .. xn] is the telescopic function
  [Π.. (t : [tele (x1 : A1) .. (xn : An)]), (tele_app B t)], where [tele_app] is
  telescopic function application as defined below.
*)
Fixpoint tele_fun (TT : tele) : (TT → Type) → Type :=
  match TT with
  | TeleO => λ T, T tt
  | @TeleS X TT' => λ T, ∀ x, tele_fun (TT' x) (λ t', T (TargS x t'))
  end.

(** Notations for the dependent and non-dependent telescopic function types.
  [Π..] is n-ary; each of the [x ... y] is a separate telescope. *)
Notation "'Π..' x .. y , P" :=
  (tele_fun _ (λ x, .. (tele_fun _ (λ y, P)) ..))
  (at level 99, x binder, y binder, right associativity,
   format "'[  ' 'Π..'  x  ..  y ']' ,  P").
Notation "TT -t> A" :=
  (Π.. x : tele_arg TT, A) (at level 99, A at level 200, right associativity).

(** A general principle for invoking non-dependent telescopic functions
    [f : TT -t> B] "step by step", i.e., dealing with one binder at a time.
    [tele_fold step f] for a telescope [x : X, y : Y, ...] expands to
    [step (λ x : X, step (λ y : Y, ... (f x y ...)))]. In other words, [step]
    is used to successively introduce all the binders, and then once
    everything is in scope, [f] is being invoked.
    The main use case is to represent repeated existential and universal
    quantification (e.g. [∀ x y z, f x y z]) using telescopes. In that case,
    [B] is a type that allows for universal or existential quantification, such
    as [Prop], Iris's [iProp] (see iris:iris:bi/lib/telescopes.v), or semantic
    interpretations of messages in Actris (see actris:actris/channel/proto.v).
    The function [step] performs a single quantification, such that [step A f]
    corresponds to [∀ x : A, f x] or [∃ x : A, f x].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition tele_fold {B} {TT : tele}
    (step : ∀ {A : Type}, (A → B) → B) (f : TT -t> B) : B :=
  (fix rec {TT} : (TT -t> B) → B :=
     match TT as TT return (TT -t> B) → B with
     | TeleO => λ f : B, f
     | TeleS b => λ f, step (λ x, rec (f x))
     end) TT f.
Global Arguments tele_fold {_ !_} _ _ /.

(** [tele_app] is used to turn a telescopic dependent function into a
  Rocq dependent function that takes a single [tele_arg TT] argument. *)
Fixpoint tele_app {TT : tele} {T : TT → Type} (F : Π.. t : TT,  T t) : ∀ t : TT, T t :=
  match TT as TT return ∀ {T : TT → Type} (F : Π.. t : TT, T t), ∀ t : TT, T t with
  | TeleO => λ T F 'tt, F
  | @TeleS X TT' => λ T F '(TeleArgCons x t'),
      @tele_app (TT' x) (λ t, T (TargS x t)) (F x) t'
  end T F.
(* The bidirectionality hint [&] simplifies defining tele_app-based notation
such as the atomic updates and atomic triples in Iris. *)
Global Arguments tele_app {!_ _} & _ !_ /.

(** Inversion lemma for [tele_arg] *)
Lemma tele_arg_inv {TT : tele} (a : TT) :
  match TT as TT return tele_arg TT → Prop with
  | TeleO => λ a, a = TargO
  | TeleS f => λ a, ∃ x a', a = TargS x a'
  end a.
Proof. destruct TT; destruct a; eauto. Qed.
Lemma tele_arg_O_inv (a : TeleO) : a = TargO.
Proof. exact (tele_arg_inv a). Qed.
Lemma tele_arg_S_inv {X} {f : X → tele} (a : TeleS f) :
  ∃ x a', a = TargS x a'.
Proof. exact (tele_arg_inv a). Qed.

(** Map below a dependent [tele_fun]. *)
Fixpoint tele_map {TT : tele} :
    ∀ {T U : TT → Type},
      (∀ t, T t → U t) →
      (Π.. t : TT, T t) →
      (Π.. t : TT, U t) :=
  match TT as TT return
      ∀ {T U : TT → Type},
        (∀ t, T t → U t) →
        (Π.. t : TT, T t) →
        (Π.. t : TT, U t) with
  | TeleO => λ T U F, F tt
  | @TeleS X TT' => λ T U F f x,
      @tele_map (TT' x) (λ t', T (TargS x t'))
        (λ t', U (TargS x t')) (λ t', F (TargS x t')) (f x)
  end.
Global Arguments tele_map {!_ _ _} _ _ /.

Lemma tele_map_app {TT : tele} {T U : TT → Type}
    (F : ∀ t, T t → U t) (f : Π.. t : TT, T t) (x : TT) :
  tele_app (tele_map F f) x = F x (tele_app f x).
Proof.
  induction TT as [|X f' IH]; simpl in *.
  - by rewrite (tele_arg_O_inv x).
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-(IH x' (λ t', T (TargS x' t')) (λ t', U (TargS x' t'))
      (λ t', F (TargS x' t')) _ a'); done.
Qed.

(** Operate below [tele_fun]s with argument telescope [TT]. *)
Fixpoint tele_bind {TT : tele} :
    ∀ {U : TT → Type}, (∀ t : TT, U t) → Π.. t : TT, U t :=
  match TT as TT return ∀ {U : TT → Type}, (∀ t : TT, U t) → Π.. t, U t with
  | TeleO => λ U F, F tt
  | @TeleS X TT' => λ U F x,
      @tele_bind (TT' x) (λ t, U (TargS x t)) (λ t, F (TargS x t))
  end.
Global Arguments tele_bind {!_ _} _ /.

(* Show that tele_app ∘ tele_bind is the identity. *)
Lemma tele_app_bind {TT : tele} {U : TT → Type} (f : ∀ t : TT, U t) x :
  tele_app (tele_bind f) x = f x.
Proof.
  induction TT as [|X b IH]; simpl in *.
  - rewrite (tele_arg_O_inv x). done.
  - destruct (tele_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
Qed.

(** We can define the identity function and composition of the [-t>] function
space. *)
Definition tele_fun_id {TT : tele} : TT -t> TT := tele_bind id.

Lemma tele_fun_id_eq {TT : tele} (x : TT) :
  tele_app tele_fun_id x = x.
Proof. unfold tele_fun_id. rewrite tele_app_bind. done. Qed.

Definition tele_fun_compose {TT1 TT2 TT3 : tele}
    (f : TT2 -t> TT3) (g : TT1 -t> TT2) : TT1 -t> TT3 :=
  tele_bind (compose (tele_app f) (tele_app g)).

Lemma tele_fun_compose_eq {TT1 TT2 TT3 : tele}
    (f : TT2 -t> TT3) (g : TT1 -t> TT2) (x : TT1) :
  tele_app (tele_fun_compose f g) x = (tele_app f ∘ tele_app g) x.
Proof. unfold tele_fun_compose. rewrite tele_app_bind. done. Qed.

(** Notation *)
Notation "'[tele' x .. z ]" :=
  (TeleS (fun x => .. (TeleS (fun z => TeleO)) ..))
  (x binder, z binder, format "[tele  '[hv' x  ..  z ']' ]").
Notation "'[tele' ]" := (TeleO)
  (format "[tele ]").

Notation "'[tele_arg' x ; .. ; z ]" :=
  (TargS x ( .. (TargS z TargO) ..))
  (format "[tele_arg  '[hv' x ;  .. ;  z ']' ]").
Notation "'[tele_arg' ]" := (TargO)
  (format "[tele_arg ]").

(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ..' x .. y , e" :=
  (tele_app (tele_bind (λ x, .. (tele_app (tele_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e") : stdpp_scope.

(** Telescopic quantifiers *)
Definition tforall {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) (tele_bind Ψ).
Global Arguments tforall {!_} _ /.
Definition texist {TT : tele} (Ψ : TT → Prop) : Prop :=
  tele_fold ex (tele_bind Ψ).
Global Arguments texist {!_} _ /.

Notation "'∀..' x .. y , P" := (tforall (λ x, .. (tforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : stdpp_scope.
Notation "'∃..' x .. y , P" := (texist (λ x, .. (texist (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P") : stdpp_scope.

Lemma tforall_forall {TT : tele} (Ψ : TT → Prop) :
  tforall Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold tforall. induction TT as [|X ft IH].
  - simpl. split.
    + done.
    + intros ? p. rewrite (tele_arg_O_inv p). done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (tele_arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

Lemma texist_exist {TT : tele} (Ψ : TT → Prop) :
  texist Ψ ↔ ex Ψ.
Proof.
  symmetry. induction TT as [|X ft IH].
  - simpl. split.
    + intros [p Hp]. rewrite (tele_arg_O_inv p) in Hp. done.
    + intros. by exists TargO.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (tele_arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH x (λ a, Ψ (TargS x a))). eauto.
    + rewrite <-(IH p (λ a, Ψ (TargS p a))).
      intros [??]. eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Global Typeclasses Opaque tforall texist.
Global Hint Extern 1 (tforall _) =>
  progress cbn [tforall tele_fold tele_bind tele_app] : typeclass_instances.
Global Hint Extern 1 (texist _) =>
  progress cbn [texist tele_fold tele_bind tele_app] : typeclass_instances.
