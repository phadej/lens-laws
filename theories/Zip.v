Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Functor.
Require Import LensLaws.These.

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

(* Require iso to be natural isomorphism *)
Parameter iso_natural : forall (A B : Set) (f : A -> B) (fa : F A),
    fmap f (isoTo (iso A) fa) = isoTo (iso B) (fmap f fa).

(* fmap on F defined via isomorphism *)
Definition fmapF {A B : Set} (f : A -> B) (x : F A) : F B.
Proof.
  apply (isoFrom (iso B)).
  apply (isoTo (iso A)) in x.
  apply (fmap f).
  exact x.
Defined.

(* Actually fmap must be equal to fmapF *)
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

(** Let us have some operation [zip] [align]. *)
Parameter zip : forall (A B : Set), F A -> F B -> F (A * B).
Parameter repeat : forall (A : Set), A -> F A.

Parameter align : forall (A B : Set), F A -> F B -> F (these A B).
Parameter nil : forall (A : Set), F A.

(* utility functions to define [zip] laws *)
Definition prod {A B C D : Set} : (A -> C) -> (B -> D) -> A * B -> C * D
  := fun f g xy => let (x, y) := xy in (f x, g y).

Definition assoc {A B C : Set} : (A * B) * C -> A * (B * C)
  := fun xyz => let (xy,z) := xyz in let (x,y) := xy in (x,(y,z)).

Definition swap {A B : Set} : A * B -> B * A
  := fun xy => let (x,y) := xy in (y,x).

Definition dup {A : Set} : A -> A * A
  := fun x => (x, x).

Definition prodT {A B C D : Set} : (A -> C) -> (B -> D) -> these A B -> these C D
  := fun f g xy =>
       match xy with
       | This x => This (f x)
       | That y => That (g y)
       | These x y => These (f x) (g y)
       end.

Definition assocT {A B C : Set} : these (these A B) C -> these A (these B C)
  := fun xyz =>
       match xyz with
       | This (This x) => This x
       | This (That y) => That (This y)
       | This (These x y) => These x (This y)
       | That z => That (That z)
       | These (This x) z => These x (That z)
       | These (That y) z => That (These y z)
       | These (These x y) z => These x (These y z)
       end.

Definition swapT {A B : Set} : these A B -> these B A
  := fun xy =>
       match xy with
       | This x => That x
       | That y => This y
       | These x y => These y x
       end.

Definition dupT {A : Set} : A -> these A A
  := fun x => These x x.

Definition fstT {A B : Set} : these A B -> option A
  := fun xy =>
       match xy with
       | This a => Some a
       | That _ => None
       | These a _ => Some a
       end.

(* [zip] laws *)
Parameter zipNaturality : forall (A B C D : Set) (x : F A) (y : F B) (f : A -> C) (g : B -> D),
  zip (fmap f x) (fmap g y) =
  fmap (prod f g) (zip x y).

Parameter zipAssociativity : forall (A B C : Set) (x : F A) (y : F B) (z : F C),
    zip x (zip y z) = fmap assoc (zip (zip x y) z).

Parameter zipSymmetry : forall (A B : Set) (x : F A) (y : F B),
    zip x y = fmap swap (zip y x).

Parameter zipIdempotency : forall (A : Set) (x : F A),
    zip x x = fmap dup x.

Parameter zipUnit : forall (A B : Set) (a : A) (x : F B),
    zip (repeat a) x = fmap (fun b => (a, b)) x.

(* [align] laws *)

Parameter alignNaturality : forall (A B C D : Set) (x : F A) (y : F B) (f : A -> C) (g : B -> D),
  align (fmap f x) (fmap g y) =
  fmap (prodT f g) (align x y).

Parameter alignAssociativity : forall (A B C : Set) (x : F A) (y : F B) (z : F C),
    align x (align y z) = fmap assocT (align (align x y) z).

Parameter alignSymmetry : forall (A B : Set) (x : F A) (y : F B),
    align x y = fmap swapT (align y x).

Parameter alignIdempotency : forall (A : Set) (x : F A),
    align x x = fmap dupT x.

Parameter alignUnit : forall (A B : Set) (x : F B),
    align (@nil A) x = fmap That x.

Parameter zip_align_Absorption : forall (A B : Set) (x : F A) (y : F B),
    fmap fst (zip x (align x y)) = x.

Parameter align_zip_Absorption : forall (A B : Set) (x : F A) (y : F B),
    fmap fstT (align x (zip x y)) = fmap Some x.

(* Conversion between Sh and F *)
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

(* mup and mdown is "inverse" forgetting contained value in F. *)
Lemma updown : forall (s : Sh),
    mdown (mup s) = s.
Proof.
  intros s.
  unfold mdown; unfold mup.
  rewrite (isoToFrom _).
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

(* mdown forgets contained values, so fmapping before mdown do nothing *)
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

(**
We can define a binary action on [Sh] using given [zip].
[M] stands for monoidal.
*)
Definition M (s z : Sh) : Sh
  := mdown (zip (mup s) (mup z)).

Definition top : Sh
  := mdown (repeat ()).

(**

Also we can define a binary action on [Sh] using [align].
[J] stands for join.
Luckily, [M] also stands for meet.

 *)

Definition J (s z : Sh) : Sh
   := mdown (align (mup s) (mup z)).

Definition bottom : Sh
   := mdown (@nil ()).



(** If [zip] behaves idempotently, then [M] is idempotent too. *)
Lemma meetIdempotency : forall (s : Sh), M s s = s.
Proof.
  intros s.
  unfold M.

  rewrite (zipIdempotency (mup s)).
  rewrite fmap_down.
  rewrite updown.
  reflexivity. Qed.

(* Also, assiciativity, commutativity, unit law follows from [zip] laws. *)
Lemma meetAssociativity : forall (s t u : Sh), M s (M t u) = M (M s t) u.
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

Lemma meetCommutativity : forall (s t : Sh), M s t = M t s.
Proof.
  intros s t.
  unfold M.
  rewrite zipSymmetry.
  rewrite (fmap_down swap).
  reflexivity.
Qed.

Lemma meetUnit : forall (s : Sh), M top s = s.
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

(** Same for [align] and [J] *)
Lemma joinIdempotency : forall (s : Sh), J s s = s.
Proof.
  intros s.
  unfold J.

  rewrite (alignIdempotency (mup s)).
  rewrite fmap_down.
  rewrite updown.
  reflexivity. Qed.

Lemma joinAssociativity : forall (s t u : Sh), J s (J t u) = J (J s t) u.
Proof.
  intros s t u.
  unfold J.
  
  rewrite ?downup.

  rewrite <- (fmap_id' (mup s)) at 1.
  rewrite <- (fmap_id' (mup u)) at 2.
  rewrite ?alignNaturality.
  rewrite alignAssociativity.
  rewrite <- (fmap_compose' _ _ _).

  rewrite ?fmap_down.
  reflexivity.
Qed.

Lemma joinCommutativity : forall (s t : Sh), J s t = J t s.
Proof.
  intros s t.
  unfold J.
  rewrite alignSymmetry.
  rewrite (fmap_down swapT).
  reflexivity.
Qed.

Lemma joinUnit : forall (s : Sh), J bottom s = s.
Proof.
  intros s.
  unfold J; unfold bottom.
  rewrite downup.
  rewrite <- (fmap_id' (mup s)).
  rewrite alignNaturality.
  rewrite alignUnit.
  rewrite ?fmap_down.
  rewrite updown.
  reflexivity.
Qed.

Lemma meet_join_Absorption : forall (s t : Sh), M s (J s t) = s.
Proof.
  intros s t.
  unfold M, J.
  rewrite downup.
  rewrite <- (fmap_id' (mup s)) at 1.
  rewrite zipNaturality.
  rewrite fmap_down.
  rewrite <- (fmap_down fst).
  rewrite zip_align_Absorption.
  rewrite updown.
  reflexivity.
Qed.

Lemma join_meet_Absorption : forall (s t : Sh), J s (M s t) = s.
Proof.
  intros s t.
  unfold M, J.
  rewrite downup.
  rewrite <- (fmap_id' (mup s)) at 1.
  rewrite alignNaturality.
  rewrite fmap_down.
  rewrite <- (fmap_down fstT).
  rewrite align_zip_Absorption.
  rewrite fmap_down.
  rewrite updown.
  reflexivity.
Qed.

End Zip.
