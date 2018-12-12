Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.These.
Require Import LensLaws.Crush.

Definition Achroma (A B : Set) : Type := { X : Set & Iso A (option X * B) }.

Lemma achroma_compose {A B C} (ab : Achroma A B) (bc : Achroma B C) : Achroma A C.
Proof.
  intros.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].

  exists (these X Y).

  set (FWD := fun (a : A) => match axb a with
    | pair ox b => match byc b with
      | pair oy c => pair (toThese ox oy) c
      end
    end).

  set (BWD := fun (z : option (these X Y) * C) => match z with
    | pair None               c => xba (pair None     (ycb (pair None c)))
    | pair (Some (This x))    c => xba (pair (Some x) (ycb (pair None c)))
    | pair (Some (That y))    c => xba (pair None     (ycb (pair (Some y) c)))
    | pair (Some (These x y)) c => xba (pair (Some x) (ycb (pair (Some y) c)))
    end).

  apply (MkIso FWD BWD); subst FWD; subst BWD.
  + crush.
  + unfold toThese; crush. Qed.

Definition achroma_select {A B} (achroma : Achroma A B) (a : A) : B.
Proof.
  destruct achroma as [X iso].
  destruct iso.
  exact (snd (f a)). Defined.

Definition achroma_upsert {A B} (achroma : Achroma A B) (oa : option A) (obb : option B -> B) : A.
Proof.
  destruct achroma as [X iso].
  destruct iso as [f g _ _ ].
  refine (match oa with
    | None   => g (pair None (obb None))
    | Some a => _
    end).

  refine (let (ox, b) := (f a) in g (pair ox (obb (Some b)))). Defined.

Definition achroma_insert {A B} (achroma : Achroma A B) (b : B) : A.
Proof.
  destruct achroma as [X iso].
  destruct iso as [f g _ _ ].
  exact (g (pair None b)). Defined.

Definition achroma_update {A B} (achroma : Achroma A B) (a : A) (b : B) : A.
Proof.
  destruct achroma as [X iso].
  destruct iso as [f g _ _ ].
  refine (match f a with
    | pair ox _ => g (pair ox b)
    end). Defined.

Theorem achroma_law1 {A B} (achroma : Achroma A B) :
  forall a b, achroma_select achroma (achroma_update achroma a b) = b.
Proof.
  intros a b. destruct achroma as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Theorem achroma_law2 {A B} (achroma : Achroma A B) :
  forall a, achroma_update achroma a (achroma_select achroma a) = a.
Proof.
  intros a. destruct achroma as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Theorem achroma_law3 {A B} (achroma : Achroma A B) :
  forall a b b', achroma_update achroma (achroma_update achroma a b') b = achroma_update achroma a b.
Proof.
  intros a b b'. destruct achroma as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Theorem achroma_law4 {A B} (achroma : Achroma A B) :
  forall b, achroma_select achroma (achroma_insert achroma b) = b.
Proof.
  intros b. destruct achroma as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Definition Dec (P : Prop) : Set := {P} + {~P}.

Theorem achroma_law5 {A B} (achroma : Achroma A B) :
  forall b b', achroma_update achroma (achroma_insert achroma b) b' = achroma_insert achroma b'.
Proof.
  intros b b'. destruct achroma as [X ab]. destruct ab as [axb xba H H0]. crush. Qed.

Theorem achroma_extra {A B} (achroma : Achroma A B) (a : A) :
  Dec (achroma_update achroma a = achroma_insert achroma).
Proof.
  destruct achroma as [X ab]. destruct ab as [axb xba H H0].
  remember (axb a) as z.
  destruct z as [ox b].
  unfold achroma_update. unfold achroma_insert.
  destruct ox as [x |].
  - right.
    unfold not. intros.
    assert (Haux : forall (f g : B -> A) (b : B), f = g -> f b = g b).
    intros f g b' R. rewrite R. trivial.
    apply Haux with (b := b) in H1.
    rewrite <- Heqz in H1.
    assert (Haux' : axb (xba (Some x, b)) = axb (xba (None, b))).
    rewrite H1. trivial.
    repeat (rewrite <- H0 in Haux').
    inversion Haux'.
  - left. rewrite <- Heqz. trivial. Defined.

(* We essentially prove that law variants are equivalent, given other laws *)
Theorem achroma_pristine_alt {A B} (achroma : Achroma A B) (a : A) :
  Dec (a = achroma_insert achroma (achroma_select achroma a)).
Proof.
  destruct (achroma_extra achroma a).
  - left.
    rewrite <- (achroma_law2 achroma) at 1. rewrite e.
    reflexivity.
  - right.
    unfold not in *. intros H1. apply n.
    rewrite H1.
    extensionality b.
    apply (achroma_law5 achroma). Qed.

Module Completeness.
  Parameter A : Set.
  Parameter B : Set.
  Parameter insert : B -> A.
  Parameter update : A -> B -> A.

  Parameter select : A -> B.

  Parameter law1 : forall a b, select (update a b) = b.
  Parameter law2 : forall a, update a (select a) = a.
  Parameter law3 : forall a b b', update (update a b') b = update a b.
  Parameter law4 : forall b, select (insert b) = b.
  Parameter law5 : forall b b', update (insert b) b' = insert b'.

  Parameter extra : forall a, Dec (update a = insert).

  Definition X : Set := {ba : B -> A | exists (a : A), ba = update a /\ update a <> insert }.

(*
  Inductive sigma (a : A) : Set := mksigma :
    forall (b : B), Dec (a = insert b) -> b = select a -> sigma a.

  Definition select'' (a : A) : sigma a.
  Proof.
    remember (select' a) as b. destruct b as [b proof].
    exists b. apply proof. unfold select. rewrite <- Heqb. exact eq_refl. Defined.
*)

  Definition FWD (a : A) : option X * B.
  Proof.
    destruct (extra a) as [_ | H].
    - refine (None, select a).
    - refine (Some _, select a).
      exists (update a). exists a. split.
      + exact (eq_refl).
      + exact H. Defined.

  Definition BWD (p : option X * B) : A.
  Proof.
    destruct p as [ox b]. destruct ox as [| x].
    - destruct x as [ba _]. exact (ba b).
    - exact (insert b). Defined.

  Theorem achroma_compete : Achroma A B.
  Proof.
    exists X.
    apply (MkIso FWD BWD); unfold FWD; unfold BWD; unfold X.

    - intros a. destruct (extra a) as [E | E].
      + rewrite <- E. symmetry. apply law2.
      + symmetry. apply law2.

    - intros p. destruct p as [ox b]. destruct ox as [x |].
      + destruct x as [ba proof].
        destruct proof as [a proof].
        destruct proof as [H H'].
        destruct (extra (ba b)) as [E | E].
        * exfalso.
          apply H'. rewrite <- E. rewrite -> H. extensionality b'. symmetry. apply law3.
        * f_equal. f_equal. subst ba.
          assert (update a = update (update a b)).
          extensionality b'. symmetry. apply law3.
          apply sigma_eq with (eqp := H).
          apply proof_irrelevance. subst ba. symmetry. apply law1.
      + destruct (extra (insert b)) as [_ | E].
        * f_equal. symmetry. apply law4.
        * exfalso. apply E. extensionality b'. apply law5. Qed.
End Completeness.
