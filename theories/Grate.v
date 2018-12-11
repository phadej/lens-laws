Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.

(* Grate *)
Definition Grate (A B : Set) : Type := { X : Set & Iso A (X -> B) }.

Lemma iso_is_grate {A B} (i : Iso A B) : Iso A (unit -> B).
Proof.
  destruct i as [f g Hfg Hgf].
  apply (MkIso
    (fun (a : A) => fun (_ : unit) => f a)
    (fun (h : unit -> B) => g (h tt))); crush.
    extensionality u. destruct u. trivial. Qed.

Lemma grate_compose {A B C} (ab : Grate A B) (bc : Grate B C) : Grate A C.
Proof.
  intros.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].

  exists (prod X Y).

  apply (MkIso
    (fun (a : A) => fun (xy : prod X Y) => byc (axb a (fst xy)) (snd xy))
    (fun (h : prod X Y -> C) => xba (fun (x : X) => ycb (fun (y : Y) => h (pair x y)))));
    crush.
  - rewrite H at 1. f_equal.
    extensionality x0.
    replace (ycb (fun y : Y => byc (axb x x0) y)) with (ycb (byc (axb x x0))).
    apply H1. f_equal.
  - extensionality xy.
    rewrite <- H2.
    crush. Qed.

Definition grate_grate {A B : Set} (grate : Grate A B) (f : (A -> B) -> B) : A.
Proof.
  destruct grate as [X i]. destruct i as [axb xba _ _].
  exact (xba (fun x : X => f (fun a : A => axb a x))). Defined.

Definition grate_indices {A B : Set} (grate : Grate A B) (a : A) (f : A -> B) : B.
Proof.
  exact (f a). Defined.


Example grate_build {A B : Set} (grate : Grate A B) (b : B) : A.
Proof.
  apply (grate_grate grate). intros _. exact b. Defined.

Example grate_set {A B : Set} (grate : Grate A B) (f : B -> B) (a : A) : A.
Proof.
  apply (grate_grate grate). intros ab. exact (f (ab a)). Defined.

Example grate_zipWith {A B : Set} (grate : Grate A B) (f : B -> B -> B) (a0 : A) (a1 : A) : A.
Proof.
  apply (grate_grate grate).
  intros ab.
  apply (f (ab a0) (ab a1)). Defined.

Example grate_unit {A : Set} : Grate unit A.
Proof.
  exists Empty_set.
  refine (MkIso
    (fun (_ : unit) (z : Empty_set) => match z return A with end)
    (fun (x : Empty_set -> A) => tt) _ _).
  Proof.
    unfold IsInverse in *.
    - crush.
    - crush.
      extensionality z. destruct z. Qed.

Example grate_unit_b {A : Set} : ( {ab : unit -> A | False } -> A) -> unit.
Proof.
  exact (fun _ => tt). Defined.

Example law1ex {A : Set} :
  forall a, a = grate_unit_b (fun ab : {ab : unit -> A | False } => match ab with exist _ ab _  => ab a end).
Proof.
  intros a. destruct a. compute. reflexivity. Qed.

Example law2ex {A : Set} :
  IsInverse grate_unit_b (fun (a : unit) (ab : { ab : unit -> A | False }) => match ab with exist _ ab _ => ab a end).
Proof.
  unfold IsInverse; unfold grate_unit_b.
  intros f.
  extensionality x.
  destruct x.
  inversion f0. Qed.

(* https://r6research.livejournal.com/28050.html *)

(*
  f ab = ab (grate f)

===>

  f ab = ab ()
*)

Theorem grate_law1 {A B} (grate : Grate A B) :
  forall a, a = grate_grate grate (grate_indices grate a).
Proof.
  intros a. destruct grate as [X i]. destruct i as [fwd bwd Hfwd Bbwd]. simpl.
  rewrite Hfwd at 1. f_equal. Qed.

(*

Theorem grate_law2 {A B} (grate : Grate A B) :
  forall idxs, idxs = grate_indices grate (grate_grate grate idxs).
Proof.
  intros f.
  destruct grate as [X i]. destruct i as [fwd bwd Hfwd Bbwd].
  unfold grate_indices; unfold grate_grate.
  extensionality idx.
  Admitted.

*)

Definition grate_I {A B} (grate : Grate A B) : Set.
Proof.
  destruct grate as [X _]. exact X. Defined.

Definition grate_index {A B} (grate : Grate A B) (a : A) (i : grate_I grate) : B.
Proof.
  destruct grate as [X iso]. destruct iso as [fwd bwd H H0].
  simpl in *.
  exact (fwd a i). Defined.

Definition grate_tabulate {A B} (grate : Grate A B) (f : grate_I grate -> B) : A.
Proof.
  destruct grate as [X iso]. destruct iso as [fwd bwd H H0].
  simpl in *.
  exact (bwd f). Defined.

Arguments grate_index {_} {_} grate a i.
Arguments grate_tabulate {_} {_} grate f.

Theorem grate_law_tabulate_index {A B} (grate : Grate A B) :
  forall a, a = grate_tabulate grate (grate_index grate a).
Proof.
  unfold grate_tabulate; unfold grate_index.
  intros a. destruct grate as [X i]. destruct i as [fwd bwd Hfwd Hbwd]. simpl.
  apply Hfwd. Qed.

Theorem grate_law_index_tabulate {A B} (grate : Grate A B) :
  forall ib i, ib i = grate_index grate (grate_tabulate grate ib) i.
Proof.
  unfold grate_tabulate; unfold grate_index.
  intros ib i. destruct grate as [X iso]. destruct iso as [fwd bwd Hfwd Hbwd]. simpl.
  crush. Qed.

Theorem grate_complete {A B : Set}
  (P : (A -> B) -> Prop)
  (grate : ((A -> B) -> B) -> A) :
  (forall a, a = grate (fun ab => ab a)) ->
  (forall ib i, ib i = i (grate ib) ) ->
  Grate A B.
Proof.
  (* intros *)
  intros law1 law2.

  set (X := A -> B).
  exists X.

  assert (FWD_test : A -> X -> B).
  refine (fun (a : A) (x : X) => x a).

  assert (BWD_test : (X -> B) -> A).
  refine (fun (xb : X -> B) => grate (fun ab => xb ab)).

  set (FWD := fun (a : A) (x : X) => x a).
  set (BWD := fun (xb : X -> B) => grate (fun ab => xb ab)).

  apply (MkIso FWD BWD); subst FWD; subst BWD; subst X.

  - intro a. apply law1.
  - unfold IsInverse. intro f. extensionality x. apply law2. Qed.

Theorem grate_complete_index_tabulate {A B I : Set}
  (index : A -> I -> B)
  (tabulate : (I -> B) -> A) :
  (forall a, a = tabulate (index a)) ->
  (forall ib i, ib i = index (tabulate ib) i) ->
  Grate A B.
Proof.
  intros law1 law2.

  set (X := I).
  exists I.

  assert (FWD_test : A -> I -> B).
  exact index.

  assert (BWD_test : (I -> B) -> A).
  exact tabulate.

  apply (MkIso index tabulate).

  - intros a. apply law1.
  - intros ib. extensionality i. apply law2. Qed.

Definition grate_P {A B : Set} (grate : Grate A B) (f : A -> B) : Prop.
Proof.
  destruct grate as [X i]. destruct i as [axb xba H0 H1].
  refine (exists (x : X), _).
  exact (f = (fun a => axb a x)). Defined.

Definition grate_grateP {A B : Set} (grate : Grate A B) (f : sig (grate_P grate) -> B) : A.
Proof.
  destruct grate as [X i]. destruct i as [axb xba H0 H1].
  unfold grate_P.
  refine (xba (fun x : X => f _)).
  exists (fun a => axb a x).
  unfold grate_P. exists x. reflexivity. Defined.

Arguments grate_grateP {_} {_} grate f.

Definition grate_indicesP {A B : Set} (grate : Grate A B) (a : A) (f : sig (grate_P grate)) : B.
Proof.
  destruct grate as [X i]. destruct i as [axb xba H0 H1].
  destruct f as [ab proof].
  exact (ab a). Defined.

Arguments grate_indicesP {_} {_} grate a f.

Theorem grate_law1P {A B} (grate : Grate A B) :
  forall a, a = grate_grateP grate (grate_indicesP grate a).
Proof.
  intros a. destruct grate as [X i]. destruct i as [fwd bwd Hfwd Bbwd]. simpl.
  rewrite Hfwd at 1. f_equal. Qed.

Theorem grate_law2P {A B} (grate : Grate A B) :
  forall idxs, idxs = grate_indicesP grate (grate_grateP grate idxs).
Proof.
  intros f.
  destruct grate as [X i]. destruct i as [fwd bwd Hfwd Hbwd]. unfold IsInverse in *.
  unfold grate_indicesP; unfold grate_grateP; unfold grate_P in *.
  extensionality idx.
  destruct idx as [idx proof]. destruct proof as [x proof].
  rewrite proof.

  set (P := fun x => exist
     (fun f0 : A -> B => exists (x0 : X), f0 = (fun a : A => fwd a x0))
     (fun a : A => fwd a x)
     (ex_intro
        (fun x0 : X => (fun a : A => fwd a x) = (fun a : A => fwd a x0)) x
        eq_refl)).

  cut (forall x : X, f (P x) = fwd (bwd (fun x0 => f (P x0))) x).

  - intros H. apply H.
  - intros P0.
    rewrite <- Hbwd. reflexivity. Qed.

(* axb := fun (a : A) (x : X) => x a *)
(* f = (fun a => axb a x) *)
Theorem grate_completeP {A B : Set}
  (P : (A -> B) -> Prop)
  (grate : ({ ab : A -> B | P ab} -> B) -> A) :
  (forall a, a = grate (fun ab => match ab with exist _ ab _ => ab a end)) ->
  (forall ib i, ib i = match i with exist _ ab _ => ab (grate ib) end) ->
  Grate A B.
Proof.
  (* intros *)
  intros law1 law2.

  set (X := sig P).
  exists X.

  assert (FWD_test : A -> X -> B).
  refine (fun (a : A) (x : X) => match x with exist _ ab _  => ab a end).

  assert (BWD_test : (X -> B) -> A).
  refine (fun (xb : X -> B) => grate (fun ab => xb ab)).

  set (FWD := fun (a : A) (x : X) => match x with exist _ ab _ => ab a end).
  set (BWD := fun (xb : X -> B) => grate (fun ab => xb ab)).

  apply (MkIso FWD BWD); subst FWD; subst BWD; subst X.

  - intro a. apply law1.
  - unfold IsInverse. intro f. extensionality x. apply law2. Qed.

Example grate_unitP {A : Set} : Grate unit A.
Proof.
  apply grate_completeP with
    (P := fun _ => False)
    (grate := fun _ => tt).
  - intros a; crush.
  - intros ib i; destruct i; crush.
    inversion f. Defined.

(* Eval compute in fun (A : Set) => grate_P (grate_unitP : Grate unit A). *)

Inductive V2 (A : Set) : Set :=
  MkV2 : A -> A -> V2 A.

Example grate_V2 {A : Set} : Grate (V2 A) A.
Proof.
  set (I1 := fun v : V2 A => match v with MkV2 x _ => x end).
  set (I2 := fun v : V2 A => match v with MkV2 _ x => x end).
  refine (@grate_completeP _ _
    (fun ab => ab = I1 \/ ab = I2)
    (fun f  => MkV2 (f (exist _ I1 _)) (f (exist _ I2 _)))
    _ _).

  - intros a. destruct a. reflexivity.
  - intros ib i. destruct i as [ab proof]. destruct proof as [proof | proof ].
    + subst ab. subst I1. simpl. reflexivity.
    + subst ab. subst I2. simpl. reflexivity. Qed.
