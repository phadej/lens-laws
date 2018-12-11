Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.

Definition Lens (A B : Set) : Type := { X : Set & Iso A (X * B) }.

Lemma iso_is_lens_ex {A B} (i : Iso A B) : Iso A (prod unit B).
Proof.
  destruct i as [f g H H0].
  apply (MkIso
    (fun (a : A) => (tt, f(a)))
    (fun (p : unit * B) => match p with (tt, b) => g b end)); crush. Defined.

Lemma iso_is_lens {A B} (i : Iso A B) : Lens A B.
Proof.
  exists unit.
  exact (iso_is_lens_ex i). Defined.

Lemma lens_compose {A B C} (ab : Lens A B) (bc : Lens B C) : Lens A C.
Proof.
  intros.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].
  exists (prod X Y).

  apply (MkIso
    (fun (a : A) => (fst (axb a), fst (byc (snd (axb a))), snd (byc (snd (axb a)))))
    (fun (t : X * Y * C) => xba (fst (fst t), ycb (snd (fst t), snd t)))); crush. Defined.

Definition lens_view {A B} (lens : Lens A B) (a : A) : B.
Proof.
  destruct lens.
  destruct i.
  exact (snd (f a)). Defined.

Definition lens_set {A B} (lens : Lens A B) (a : A) (b : B) : A.
Proof.
  destruct lens.
  destruct i.
  exact (g (fst (f a), b)). Defined.

Theorem lens_law1 {A B} (lens : Lens A B) :
  forall a b, lens_view lens (lens_set lens a b) = b.
Proof.
  intros a b. destruct lens as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Theorem lens_law2 {A B} (lens : Lens A B) :
  forall a, lens_set lens a (lens_view lens a) = a.
Proof.
  intros a. destruct lens as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Lemma lens_law3_weak {A B} (lens : Lens A B) :
  forall a b, lens_set lens (lens_set lens a b) b = lens_set lens a b.
Proof.
  intros a b.
  assert (
    lens_set lens (lens_set lens a b) b =
    lens_set lens (lens_set lens a b) (lens_view lens (lens_set lens a b))).
    f_equal. symmetry. apply lens_law1.
  rewrite H.
  rewrite lens_law2.
  reflexivity. Qed.

Theorem lens_law3 {A B} (lens : Lens A B) :
  forall a b b', lens_set lens (lens_set lens a b') b = lens_set lens a b.
Proof.
  intros a b b'. destruct lens as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Lemma sigma_eq {A} {P : A -> Prop} (x y : A) (px : P x) (py : P y) (eqp : x = y) :
  (eq_ind x P px y eqp = py) ->
  exist P x px = exist P y py.
Proof.
  intros. subst. f_equal. Qed.

Theorem lens_complete {A B : Set} (view : A -> B) (set : A -> B -> A):
  (forall a b, view (set a b) = b) ->
  (forall a, set a (view a) = a) ->
  (forall a b b', set (set a b) b' = set a b') ->
  Lens A B.
Proof.
  intros law1 law2 law3.

  exists ({ba : B -> A | exists (a : A), ba = set a}).

  (* This definitions help to find right forms *)
  (*
  assert (FWD: A -> {ba : B -> A | exists (a : A), ba = set a} * B).
  refine
    (fun (a : A) => (exist _ (set a) (ex_intro _ a eq_refl), view a)).
  assert (BWD: {ba : B -> A | exists (a : A), ba = set a} * B -> A).
  refine
    (fun p => match p as A with (exist _ ba _, b) => ba b end).
  *)

  set (FWD := fun (a : A) => (exist (fun ba => exists (a : A), ba = set a) (set a) (ex_intro (fun x => set a = set x) a eq_refl), view a)).
  set (BWD := fun (p : {ba : B -> A | exists (a : A), ba = set a} * B) => match p as A with (exist _ ba _, b) => ba b end).

  apply (MkIso FWD BWD); subst FWD; subst BWD.

  - intro a; simpl. symmetry. apply law2.
  - intro p. destruct p as [ba b]; destruct ba as [ba Hba]. destruct Hba as [a Hba].
    f_equal.
    + simpl. subst. symmetry.
      assert (set (set a b) = set a) as Hsetset.
      extensionality b'. apply law3.
      apply sigma_eq with (eqp := Hsetset).
      apply proof_irrelevance.
    + rewrite Hba. symmetry. apply law1. Qed.
