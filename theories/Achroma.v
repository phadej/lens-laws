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

(*
Theorem achroma_complete {A B : Set} (select : A -> B) (upsert : option A -> (option B -> B) -> A):
  1 = 1 ->
  Achroma A B.
Proof.
  intros law1.

  set (X := (option B -> B) -> A).
  exists X.

  assert (FWD_test : A -> option X * B).
  refine (fun (a : A) => _).
  split.

*)
