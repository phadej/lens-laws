Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Functor.

Module Zip.

Parameter F : Set -> Set.

(** Shape *)
Parameter Sh : Set.

(** Index *)
Parameter Ix : Sh -> Set.

(** Container *)
Definition C (A : Set) : Set := sigT (fun (s : Sh) => Ix s -> A).

(** Iso *)
Parameter iso : forall (X : Set), Iso (F X) (C X).

Definition fmapF {A B : Set} (f : A -> B) (x : F A) : F B.
Proof.
  apply (isoFrom (iso B)).
  apply (isoTo (iso A)) in x.
  destruct x as [s ia].
  exists s. intros i.
  apply f. apply ia. exact i. Defined.

(** [F] is a functor. *)
Theorem functorF : IsFunctor F.
Proof.
  apply (@MkFunctor F (@fmapF)).

  - intros A.
    extensionality x.
    unfold fmapF. unfold isoFrom. unfold isoTo.
    destruct (iso A).
    unfold IsInverse in *.
    rewrite (i x) at 2.
    f_equal.
    destruct (f x).
    f_equal.

  - intros A B C' f g.
    extensionality x.
    unfold fmapF. unfold isoFrom. unfold isoTo.
    destruct (iso A) as [fwdA bwdA HA HA'].
    destruct (iso C') as [fwdC bwdC HC HC'].
    destruct (iso B) as [fwdB bwdB HB HB'].
    rewrite <- HB'.
    f_equal. destruct (fwdA x). trivial. Defined.

(** Let us have some operation [zip]. *)
Parameter zip : forall (A B : Set) (x : F A) (y : F B), F (A * B).

(*
Parameter Naturality : forall (A B C D : Set) (x : F A) (y : F B) (f : A -> C) (g : B -> D),
  zip (fmapF f x) (fmapF g y) =
  fmapF (fun (xy : A * B) => let (x', y') := xy in (f x', g y')) (zip x y).
*)

(**
We can define a binary action on [Sh] using given [zip].
[M] stands for monoidal.
*)
Definition M (s z : Sh) : Sh.
Proof.
  set (cx := fun (i : Ix s) => tt).
  set (cy := fun (i : Ix z) => tt).

  set (fx := isoFrom (iso ()) (@existT Sh _ s cx)).
  set (fy := isoFrom (iso ()) (@existT Sh _ z cy)).

  set (fxy := zip fx fy).
  set (cxy := isoTo (iso _) fxy).

  destruct cxy as [sz _].
  exact sz. Defined.

(** If [zip] behaves idempotently, then [M] is idempotent too. *)
Lemma Idempotency :
  (forall (A : Set) (xs : F A), zip xs xs = fmapF (fun x => (x, x)) xs) ->
  (forall (s : Sh), M s s = s).
Proof.
  intros H s.
  unfold M.

  (** we use assumption immediately *)
  rewrite H.

  (** rest is mechanic *)
  unfold fmapF; unfold isoTo; unfold isoFrom.

  destruct (iso (() * ())) as [fwdP bwdP HP HP'].
  rewrite <- HP'.
  destruct (iso ()) as [fwdU bwdU HU HU'].
  rewrite  <- HU'.

  reflexivity. Qed.

End Zip.
