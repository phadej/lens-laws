Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.

Definition Prism (A B : Set) : Type := { X : Set & Iso A (X + B) }.

Lemma iso_is_prism_ex {A B} (i : Iso A B) : Iso A (sum Empty_set B).
Proof.
  destruct i as [f g H H0].
  apply (MkIso
    (fun (a : A) => inr(f(a)))
    (fun  (e : Empty_set + B) =>
      match e with
      | inr b => g b
      | inl void => Empty_set_rec _ void
      end)); crush. Defined.

Lemma iso_is_prism {A B} (i : Iso A B) : Prism A B.
Proof.
  intros.
  exists Empty_set.
  exact (iso_is_prism_ex i). Defined.

Lemma prism_compose {A B C} (ab : Prism A B) (bc : Prism B C) : Prism A C.
Proof.
  intros.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].
  exists (sum X Y).

  apply (MkIso
    (fun (a : A) =>
      match axb a with
      | inl x => inl (inl x)
      | inr b =>
        match byc b with
        | inl y => inl (inr y)
        | inr b => inr b
        end
      end)
    (fun (t : X + Y + C) =>
      match t with
      | inl xy =>
        match xy with
        | inl x => xba (inl x)
        | inr y => xba (inr (ycb (inl y)))
        end
      | inr c => xba (inr (ycb (inr c)))
      end)); crush. Qed.

Definition prism_review {A B} (prism : Prism A B) (b : B) : A.
Proof.
  destruct prism as [Y ab]. destruct ab as [ayb yba _ _].
  exact (yba (inr b)). Defined.

Definition prism_preview {A B} (prism : Prism A B) (a : A) : option B.
Proof.
  destruct prism as [Y ab]. destruct ab as [ayb yba _ _].
  destruct (ayb a) as [y | b].
  exact None. exact (Some b). Defined.

Theorem prism_law1 {A B} (prism : Prism A B) :
  forall (b : B), prism_preview prism (prism_review prism b) = Some b.
Proof.
  intros b. destruct prism as [Y ab]. destruct ab as [ayb yba H H0]. crush. Qed.

Theorem prism_law2 {A B} (prism : Prism A B) :
  forall a b, prism_preview prism a = Some b -> prism_review prism b = a.
Proof.
  intros a b Hsome. destruct prism as [Y ab]. destruct ab as [ayb yba H H0].
  crush. Qed.

Theorem prism_law3_variant {A B} (prism : Prism A B) :
  forall a, prism_preview prism a = None -> (forall b, prism_review prism b <> a).
Proof.
  intros a Hnone. destruct prism as [Y ab]. destruct ab as [ayb yba H H0]. unfold not.
  crush.
  - rewrite (H a) in H1.
    assert (Contra : ayb (yba (inr b)) = ayb (yba (inl y))).
    rewrite H1. rewrite Heqayba. reflexivity.
    repeat (rewrite <- H0 in Contra).
    inversion Contra.
  - inversion Hnone. Qed.

Theorem prism_complete {A B : Set} (review : B -> A) (preview : A -> option B):
  (forall b, preview (review b) = Some b) ->
  (forall a b, preview a = Some b -> review b = a) ->
  Prism A B.
Proof.
  intros law1 law2.

  set (E := { a : A | None = preview a }).

  exists E.

  assert (FWD: A -> E + B).
  refine (fun (a : A) =>
    let pa := preview a in
    let Heqpa := eq_refl : pa = preview a in
    (match pa as pa0 return (pa0 = preview a -> E + B) with
      | None   => fun proof => inl (exist _ a proof)
      | Some b => fun _  => inr b
      end) Heqpa).

  assert (BWD: E + B -> A).
  refine (fun (eb : E + B) => match eb with
    | inl (exist _ a _) => a
    | inr b => review b
    end).

  set (FWD2 := (fun (a : A) =>
    let pa := preview a in
    let Heqpa := eq_refl : pa = preview a in
    (match pa as pa0 return (pa0 = preview a -> E + B) with
      | None   => fun proof => inl (exist _ a proof)
      | Some b => fun _  => inr b
      end) Heqpa)).
  set (BWD2 := (fun (eb : E + B) => match eb with
    | inl (exist _ a _) => a
    | inr b => review b
    end)).

  apply (MkIso FWD2 BWD2); subst E; subst FWD2; subst BWD2.

  - intro a. simpl.
    rewrite (@dependentMatchOfMatch _ (fun o => o = preview a) A (preview a) eq_refl _ _ (fun b pf => inr b) (fun pf => inl (exist (fun a0 : A => None = preview a0) a pf))).
    remember (preview a) as pa.
    destruct pa.
    + symmetry. apply law2. symmetry. apply Heqpa.
    + trivial.
  - intro eb. simpl. destruct eb as [e | b]; simpl.
    + destruct e as [a Hnone].
      set (Lem2 := @lem2_None _ ({ a : A | None = preview a } + B) (preview a)            Hnone).             rewrite Lem2. reflexivity.
    + set (Lem2 := @lem2_Some _ ({ a : A | None = preview a } + B) (preview (review b)) b (eq_sym (law1 b))). rewrite Lem2. reflexivity. Qed.
