Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Functor.
Require Import LensLaws.These.

Module ReZip.

(** Shape *)
Parameter Sh : Set.

(** Shape is Lattice *)
Parameter meet : Sh -> Sh -> Sh.
Parameter join : Sh -> Sh -> Sh.
Parameter top : Sh.
Parameter bottom : Sh.

Axiom meet_associative :
  forall (x y z : Sh), meet x (meet y z) = meet (meet x y) z.
Axiom meet_commutative :
  forall (x y : Sh), meet x y = meet y x.
Axiom meet_top :
  forall (x : Sh), meet top x = x.
Axiom join_associative :
  forall (x y z : Sh), join x (join y z) = join (join x y) z.
Axiom join_commutative :
  forall (x y : Sh), join x y = join y x.
Axiom join_bottom :
  forall (x : Sh), join bottom x = x.
Axiom meet_join_absorption :
  forall (x y : Sh), meet x (join x y) = x.
Axiom join_meet_absorption :
  forall (x y : Sh), join x (meet x y) = x.

Theorem meet_idempotent :
  forall (x : Sh), meet x x = x.
Proof.
  intros x.
  rewrite <- (join_meet_absorption x x) at 2.
  rewrite meet_join_absorption.
  reflexivity.
Qed.

Theorem join_idempotent :
  forall (x : Sh), join x x = x.
Proof.
  intros x.
  rewrite <- (meet_join_absorption x x) at 2.
  rewrite join_meet_absorption.
  reflexivity.
Qed.

(** Index *)
Parameter U : Set.
Parameter Ix : Sh -> U -> bool.

(** Lattice structure maps to indices *)
Axiom meet_to_intersection :
  forall (s t : Sh) (u : U), Ix (meet s t) u = andb (Ix s u) (Ix t u).
Axiom join_to_union :
  forall (s t : Sh) (u : U), Ix (join s t) u = orb (Ix s u) (Ix t u).

Axiom top_index : forall (u : U), Ix top u = true.
Axiom bottom_index : forall (u : U), Ix bottom u = false.

(** Container
    Note that Con A ~ sigT (fun s => { u:U | Ix s u = true } -> A).
*)
Definition Con (A : Set) : Set :=
  sigT (fun (s : Sh) => forall (u : U), Ix s u = true -> A).

Instance FunctorCon : IsFunctor Con := {}.
Proof.
  (* fmap *)
  - intros A B f ca.
    destruct ca as [s p].
    exists s.
    intros u H.
    exact (f (@p u H)).
  (* fmap_id *)
  - intros A.
    extensionality cx.
    destruct cx as [s p].
    reflexivity.
  (* fmap_compose *)
  - intros A B C f g.
    extensionality cx.
    destruct cx as [s p].
    reflexivity.
Defined.

Lemma and_conj : forall (a b : bool),
    (andb a b = true) -> (a = true /\ b = true).
Proof.
  intros a b H.
  destruct a; destruct b; discriminate || auto.
Defined.

(** Let us have some operation [zip] [align]. *)
Definition zip {A B : Set} : Con A -> Con B -> Con (A * B).
Proof.
  intros ca cb.
  destruct ca as [s p].
  destruct cb as [t q].
  exists (meet s t).
  intros u H.
  rewrite meet_to_intersection in H.
  apply and_conj in H.
  destruct H as [Hs Ht].
  exact (@p u Hs,@q u Ht).
Defined.

Definition repeat {A : Set} : A -> Con A.
Proof.
  intros a.
  exists top.
  intros _ _.
  exact a.
Defined.

Definition or_disj : forall (a b : bool),
    orb a b = true -> (a = true /\ b = true) + (a = true /\ b = false) +
                      (a = false /\ b = true).
Proof.
  intros a b H.
  destruct a; destruct b.
  - left; left. exact (conj eq_refl eq_refl).
  - left; right. exact (conj eq_refl eq_refl).
  - right. exact (conj eq_refl eq_refl).
  - discriminate H.
Defined.

Definition align {A B : Set} : Con A -> Con B -> Con (these A B).
Proof.
  intros ca cb.
  destruct ca as [s p].
  destruct cb as [t q].
  exists (join s t).
  intros u H.
  rewrite join_to_union in H.
  apply or_disj in H.
  destruct H as [[H1 | H2] | H3].
  - destruct H1 as [Es Et].
    set (a := @p u Es).
    set (b := @q u Et).
    exact (These a b).
  - destruct H2 as [Es Et].
    set (a := @p u Es).
    exact (This a).
  - destruct H3 as [Es Et].
    set (b := @q u Et).
    exact (That b).
Defined.

Definition nil {A : Set} : Con A.
Proof.
  exists bottom.
  intros u H.
  rewrite bottom_index in H.
  discriminate.
Defined.

(* utility functions to define [zip] [align] laws *)
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

(* Equivalence between Con *)
Definition mkCon {A : Set} (s : Sh) (p : forall u, Ix s u = true -> A) : Con A
  := existT (fun s0 => forall u, Ix s0 u = true -> A) s p.

Let eqto {s t : Sh} (e : s = t) :
  forall u, Ix s u = true -> Ix t u = true.
Proof.
  intros u H.
  rewrite e in H.
  exact H.
Defined.

Inductive semieq {A : Set} : Con A -> Con A -> Prop :=
  semiEq_intro :
    forall (s t : Sh) (eqst : s = t),
      forall (p : forall u, Ix s u = true -> A)
             (q : forall u, Ix t u = true -> A),
        (forall (u:U) (H : Ix s u = true), p u H = q u (eqto eqst H)) ->
        semieq (mkCon p) (mkCon q).

Notation "x === y" := (semieq x y) (at level 100).

Ltac semieq_with eqst :=
  apply (@semiEq_intro _ _ _ eqst).

(* semieq is Equivalence relation *)
Theorem semieq_reflexivity :
  forall (A : Set) (x : Con A),
    x === x.
Proof.
  intros A [x p].
  semieq_with (eq_refl : x = x).
  intros u H.
  f_equal.
Qed.

Theorem semieq_symmetry :
  forall (A : Set) (x y : Con A),
    (x === y) -> (y === x).
Proof.
  intros A x y H.
  destruct H as [x y E p q H].
  semieq_with (eq_sym E).
  intros u B.
  rewrite (proof_irrelevance _ B (eqto E (eqto (eq_sym E) B))) at 1.
  symmetry.
  apply H.
Qed.

Theorem semieq_transitivity :
  forall (A : Set) (x y z : Con A),
    (x === y) -> (y === z) -> (x === z).
Proof.
  intros A [x p] [y q] [z r] Hxy Hyz.
  inversion Hxy as [x' y' Exy p' q' Hxy' [Tx Tp] [Ty Tq]].
  inversion Hyz as [y'' z'' Eyz q'' r'' Hyz' [Ry Rq] [Rz Rr]].
  dependent destruction Tp.
  dependent destruction Rr.
  semieq_with Eyz.
  intros u H.
  rewrite Hxy'.
  rewrite <- Hyz'.
  reflexivity.
Qed.

(* [zip] laws *)
Theorem zipNaturality : forall (A B C D : Set) (x : Con A) (y : Con B) (f : A -> C) (g : B -> D),
  zip (fmap f x) (fmap g y) =
  fmap (prod f g) (zip x y).
Proof.
  intros A B C D x y f g.
  unfold fmap, FunctorCon, zip.
  destruct x as [s p].
  destruct y as [t q].
  unfold prod.
  unfold zip.
  f_equal.
  extensionality u; extensionality H.
  destruct and_conj as [Es Et].
  reflexivity.
Qed.

Theorem zipIdempotency : forall (A : Set) (x : Con A),
    zip x x === fmap dup x.
Proof.
  intros A x.
  unfold fmap, FunctorCon, zip.
  destruct x as [s p].
  assert (meet s s = s) as E by apply meet_idempotent.
  semieq_with E.
  intros u H.
  destruct and_conj as [Hs Ht].
  rewrite (proof_irrelevance _ Hs (eqto E H)).
  rewrite (proof_irrelevance _ Ht (eqto E H)).
  reflexivity.
Qed.

Theorem zipSymmetry : forall (A B : Set) (x : Con A) (y : Con B),
    zip x y === fmap swap (zip y x).
Proof.
  intros A B [x p] [y q].
  unfold fmap, FunctorCon, zip.
  assert (meet x y = meet y x) as E by apply meet_commutative.
  semieq_with E.
  intros u H.
  destruct and_conj as [Hx1 Hy1].
  destruct and_conj as [Hy2 Hx2].
  rewrite (proof_irrelevance _ Hx1 Hx2).
  rewrite (proof_irrelevance _ Hy1 Hy2).
  reflexivity.
Qed. 

Theorem zipAssociativity : forall (A B C : Set) (x : Con A) (y : Con B) (z : Con C),
    zip x (zip y z) === fmap assoc (zip (zip x y) z).
Proof.
  intros A B C [x p] [y q] [z r].
  unfold fmap, FunctorCon, zip.
  assert (meet x (meet y z) = meet (meet x y) z) as E  by apply meet_associative.
  semieq_with E.
  intros u H.
  destruct and_conj as [Hx1 Hyz1].
  destruct and_conj as [Hy1 Hz1].
  destruct and_conj as [Hxy2 Hz2].
  destruct and_conj as [Hx2 Hy2].
  rewrite (proof_irrelevance _ Hx1 Hx2).
  rewrite (proof_irrelevance _ Hy1 Hy2).
  rewrite (proof_irrelevance _ Hz1 Hz2).
  reflexivity.
Qed.  

Theorem zipUnit : forall (A : Set) (a : A) (x : Con A),
    zip (repeat a) x === fmap (fun x => (a, x)) x.
Proof.
  intros A a [x p].
  unfold fmap; unfold FunctorCon; unfold zip; unfold repeat.
  assert (meet top x = x) as E by apply meet_top.
  semieq_with E.
  intros u H.
  destruct and_conj as [_ Hx].
  rewrite (proof_irrelevance _ Hx (eqto E H)).
  reflexivity.
Qed.


(** [align] laws *)
Theorem alignNaturality : forall (A B C D : Set) (x : Con A) (y : Con B) (f : A -> C) (g : B -> D),
  align (fmap f x) (fmap g y) =
  fmap (prodT f g) (align x y).
Proof.
  intros A B C D x y f g.
  unfold fmap, FunctorCon, align.
  destruct x as [x p].
  destruct y as [y q].
  f_equal.
  extensionality u.
  extensionality H.
  unfold prodT.
  destruct or_disj as [[EE | EE] | EE]; destruct EE as [Es Et]; reflexivity.
Qed.

Theorem alignIdempotency : forall (A : Set) (x : Con A),
    align x x === fmap dupT x.
Proof.
  intros A x.
  destruct x as [s p].
  unfold align; unfold FunctorCon; unfold zip.
  assert (join s s = s) as E by apply join_idempotent.
  semieq_with E.
  intros u H.
  destruct or_disj as [[EE | EE] | EE]; destruct EE as [Es Et].
  - rewrite (proof_irrelevance _ Es (eqto E H)).
    rewrite (proof_irrelevance _ Et (eqto E H)).
    reflexivity.
  - rewrite Es in Et. discriminate Et.
  - rewrite Et in Es. discriminate Es.
Qed.

Theorem alignSymmetry : forall (A B : Set) (x : Con A) (y : Con B),
    align x y === fmap swapT (align y x).
Proof.
  intros A B [x p] [y q].
  unfold fmap, FunctorCon, align.
  assert (join x y = join y x) as E by apply join_commutative.
  semieq_with E.
  intros u H.
  destruct or_disj as [[EE | EE] | EE]; destruct EE as [Ex1 Ey1];
    destruct or_disj as [[EE | EE] | EE]; destruct EE as [Ey2 Ex2];
      try congruence.
  - rewrite (proof_irrelevance _ Ex1 Ex2);
    rewrite (proof_irrelevance _ Ey1 Ey2);
    reflexivity.
  - rewrite (proof_irrelevance _ Ex1 Ex2).
    reflexivity.
  - rewrite (proof_irrelevance _ Ey1 Ey2).
    reflexivity.
Qed.

Theorem alignAssociativity : forall (A B C : Set) (x : Con A) (y : Con B) (z : Con C),
    align x (align y z) === fmap assocT (align (align x y) z).
Proof.
  intros A B C [x p] [y q] [z r].
  unfold fmap, FunctorCon, align.
  assert (join x (join y z) = join (join x y) z) as E by apply join_associative.
  semieq_with E.
  intros u H.
  destruct or_disj as [[EE | EE] | EE]; destruct EE as [E1 E2];
    destruct or_disj as [[EE | EE] | EE]; destruct EE as [E3 E4];
      try (destruct or_disj as [[EE | EE] | EE]; destruct EE as [E5 E6]);
        try (destruct or_disj as [[EE | EE] | EE]; destruct EE as [E7 E8]);
          try congruence;
          try (unfold assocT; f_equal; f_equal; f_equal; apply proof_irrelevance).
  - rewrite join_to_union in E5.
    rewrite E1 in E5.
    discriminate E5.
  - rewrite join_to_union in E5.
    rewrite E1 in E5.
    discriminate E5.
  - rewrite join_to_union in E2.
    rewrite E6 in E2.
    discriminate E2.
  - rewrite join_to_union in E2.
    rewrite E4 in E2.
    destruct (Ix y u); discriminate E2.
  - rewrite join_to_union in E2.
    rewrite E6 in E2.
    discriminate E2.
  - rewrite join_to_union in E3.
    rewrite E1 in E3.
    discriminate E3.
  - rewrite join_to_union in E5.
    rewrite E3 in E5.
    destruct (Ix x u); discriminate E5.
Qed.

Theorem alignUnit : forall (A B : Set) (x : Con A),
    align (@nil B) x === fmap That x.
Proof.
  intros A B [x p].
  unfold fmap, FunctorCon, align, nil.
  assert (join bottom x = x) as E by apply join_bottom.
  semieq_with E.
  intros u H.
  destruct or_disj as [[EE | EE] | EE]; destruct EE as [Ebot Ex].
  - contradict Ebot.
    rewrite bottom_index.
    discriminate.
  - contradict Ebot.
    rewrite bottom_index.
    discriminate.
  - rewrite (proof_irrelevance _ Ex (eqto E H)).
    reflexivity.
Qed.

(* [zip] and [align] together *)
Theorem zip_align_Absorption : forall (A B : Set) (x : Con A) (y : Con B),
    fmap fst (zip x (align x y)) === x.
Proof.
  intros A B [x p] [y q].
  unfold fmap, FunctorCon, zip, align.
  assert (meet x (join x y) = x) as E by apply meet_join_absorption.
  semieq_with E.
  intros u H.
  destruct and_conj as [Ex Exy].
  unfold fst.
  f_equal.
  apply proof_irrelevance.
Qed.

Theorem align_zip_Absorption : forall (A B : Set) (x : Con A) (y : Con B),
    fmap fstT (align x (zip x y)) === fmap Some x.
Proof.
  intros A B [x p] [y q].
  unfold fmap, FunctorCon, align, zip.
  assert (join x (meet x y) = x) as E by apply join_meet_absorption.
  semieq_with E.
  intros u H.
  destruct or_disj as [[E1 | E2] | E3].
  - destruct E1 as [Ex Ey].
    unfold fstT.
    f_equal; f_equal.
    apply proof_irrelevance.
  - destruct E2 as [Ex Ey].
    unfold fstT.
    f_equal; f_equal.
    apply proof_irrelevance.
  - destruct E3 as [Ex Ey].
    contradict Ey.
    rewrite meet_to_intersection.
    rewrite Ex.
    discriminate.
Qed.

End ReZip.
