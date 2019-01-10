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
Parameter FunctorF : IsFunctor F.

(** Shape *)
Parameter Sh : Set.

(** Index *)
Parameter Ix : Sh -> Set.

(** Container *)
Definition C (A : Set) : Set := sigT (fun (s : Sh) => Ix s -> A).

Instance FunctorC : IsFunctor C := {}.
Proof.
  (* fmap *)
  - intros A B f ca.
    destruct ca as [s u].
    exists s.
    exact (fun i => f (u i)).
  (* fmap_id *)
  - intros A.
    extensionality cx.
    destruct cx as [s u].
    reflexivity.
  (* fmap_compose *)
  - intros A B C f g.
    extensionality cx.
    destruct cx as [s u].
    reflexivity.
Defined.

(** Iso *)
Parameter iso : forall (X : Set), Iso (F X) (C X).

Parameter iso_natural : forall (A B : Set) (f : A -> B) (fa : F A),
    fmap f (isoTo (iso A) fa) = isoTo (iso B) (fmap f fa).

Definition fmapF {A B : Set} (f : A -> B) (x : F A) : F B.
Proof.
  apply (isoFrom (iso B)).
  apply (isoTo (iso A)) in x.
  apply (fmap f).
  exact x.
Defined.

Theorem fmapF_canonical {A B : Set} :
  fmap = @fmapF A B.
Proof.
  extensionality f.
  extensionality fx.
  unfold fmapF.
  apply isoMove.
  symmetry.
  apply iso_natural.
Qed.

(** Let us have some operation [zip]. *)
Parameter zip : forall (A B : Set) (x : F A) (y : F B), F (A * B).
Parameter topF : F ().

Definition prod {A B C D : Set} : (A -> C) -> (B -> D) -> A * B -> C * D
  := fun f g xy => let (x, y) := xy in (f x, g y).

Definition assoc {A B C : Set} : (A * B) * C -> A * (B * C)
  := fun xyz => let (xy,z) := xyz in let (x,y) := xy in (x,(y,z)).

Definition swap {A B : Set} : A * B -> B * A
  := fun xy => let (x,y) := xy in (y,x).

Definition dup {A : Set} : A -> A * A
  := fun x => (x, x).

Parameter zipNaturality : forall (A B C D : Set) (x : F A) (y : F B) (f : A -> C) (g : B -> D),
  zip (fmap f x) (fmap g y) =
  fmap (prod f g) (zip x y).

Parameter zipAssociativity : forall (A B C : Set) (x : F A) (y : F B) (z : F C),
    zip x (zip y z) = fmap assoc (zip (zip x y) z).

Parameter zipSymmetry : forall (A B : Set) (x : F A) (y : F B),
    zip x y = fmap swap (zip y x).

Parameter zipIdempotency : forall (A : Set) (x : F A),
    zip x x = fmap dup x.

Parameter zipUnit : forall (A : Set) (x : F A),
    zip topF x = fmap (fun x => ((), x)) x.

Definition mup (s : Sh) : F ().
Proof.
  apply (isoFrom (iso ())).
  exact (@existT Sh _ s (fun (i : Ix s) => tt)).
Defined.

Definition mdown {A : Set} (fx : F A) : Sh.
Proof.
  destruct (isoTo (iso A) fx) as [s _].
  exact s.
Defined.

Lemma updown : forall (s : Sh),
    mdown (mup s) = s.
Proof.
  intros s.
  unfold mdown; unfold mup.
  rewrite (isoToFrom _).
  reflexivity.
Qed.

Lemma fmap_down : forall {A B : Set} (f : A -> B) (fx : F A),
    mdown (fmap f fx) = mdown fx.
Proof.
  intros A B f fx.
  rewrite fmapF_canonical.
  unfold mdown; unfold fmapF.
  rewrite (isoToFrom _).
  destruct (isoTo (iso A) fx).
  reflexivity.
Qed.

Lemma downup : forall (A : Set) (fx : F A),
    mup (mdown fx) = fmap (fun _ => tt) fx.
Proof.
  intros A fx.
  rewrite fmapF_canonical.
  unfold mdown; unfold mup.
  unfold fmapF.
  f_equal.
  destruct (isoTo (iso A) fx) as [s u].
  reflexivity.
Qed.

(**
We can define a binary action on [Sh] using given [zip].
[M] stands for monoidal.
*)
Definition M (s z : Sh) : Sh
  := mdown (zip (mup s) (mup z)).

Definition top : Sh
  := mdown topF.

(** If [zip] behaves idempotently, then [M] is idempotent too. *)
Lemma Idempotency : forall (s : Sh), M s s = s.
Proof.
  intros s.
  unfold M.

  rewrite (zipIdempotency (mup s)).
  rewrite fmap_down.
  rewrite updown.
  reflexivity. Qed.

Lemma Associativity : forall (s t u : Sh), M s (M t u) = M (M s t) u.
Proof.
  intros s t u.
  unfold M.
  
  rewrite ?downup.

  rewrite <- (fmap_id' (mup s)) at 1.
  rewrite <- (fmap_id' (mup u)) at 2.
  rewrite ?zipNaturality.
  rewrite zipAssociativity.
  rewrite <- (fmap_compose' _ _ _).

  rewrite ?fmap_down.
  reflexivity.
Qed.

Lemma Commutativity : forall (s t : Sh), M s t = M t s.
Proof.
  intros s t.
  unfold M.
  rewrite zipSymmetry.
  rewrite (fmap_down swap).
  reflexivity.
Qed.

Lemma MUnit : forall (s : Sh), M top s = s.
Proof.
  intros s.
  unfold M; unfold top.
  rewrite downup.
  rewrite <- (fmap_id' (mup s)).
  rewrite zipNaturality.
  rewrite zipUnit.
  rewrite ?fmap_down.
  rewrite updown.
  reflexivity.
Qed.

End Zip.
