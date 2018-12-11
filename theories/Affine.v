Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.
Require Import LensLaws.Lens.
Require Import LensLaws.Prism.

(* Affine Traversal *)
Definition Affine (A B : Set) : Type := { XY : prod Set Set & Iso A (fst XY + (snd XY * B)) }.

Lemma lens_is_affine {A B} (lens : Lens A B) : Affine A B.
Proof.
  destruct lens as [X i].
  exists (pair Empty_set X). simpl.
  apply iso_is_prism_ex. apply i. Defined.

Lemma iso_right {A B X : Set} (i : Iso A B) : Iso (X + A) (X + B).
Proof.
  destruct i as [f g H H0].

  assert (sum X A -> sum X B) as xaxb.
  apply (fun xa =>
    match xa with
    | inl x => inl x
    | inr a => inr (f a)
    end).
  assert (sum X B -> sum X A) as xbxa.
  apply (fun xb =>
    match xb with
    | inl x => inl x
    | inr b => inr (g b)
    end).

  apply (@MkIso (X + A) (X + B)
    (fun xa =>
      match xa with
      | inl x => inl x
      | inr a => inr (f a)
      end)
    (fun xb =>
      match xb with
      | inl x => inl x
      | inr b => inr (g b)
      end)); crush. Defined.

Lemma prism_is_affine {A B} (prism : Prism A B) : Affine A B.
Proof.
  destruct prism as [X i].
  exists (pair X unit). simpl.

  destruct i as [f g H H0].

  assert (A -> X + unit * B).
  refine (fun a =>
    match f a with
    | inl x => inl x
    | inr b => inr (pair tt b)
    end).
  assert (X + unit * B -> A).
  refine (fun xub =>
    g (match xub with
    | inl x => inl x
    | inr ub => inr (snd ub)
    end)).

  apply (MkIso
    (fun a =>
      match f a with
      | inl x => inl x
      | inr b => inr (pair tt b)
      end)
    (fun xub =>
      g (match xub with
      | inl x => inl x
      | inr ub => inr (snd ub)
      end))); crush. Defined.

Lemma prism_lens_compose {A B C} (ab : Prism A B) (bc : Lens B C) : Affine A C.
Proof.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].
  exists (pair X Y); simpl.

  assert (A -> X + Y * C).
  refine
    (fun a =>
      match axb a with
      | inl x => inl x
      | inr b => inr (byc b)
      end).

  assert (X + Y * C -> A).
  refine
    (fun xyc =>
      match xyc with
      | inl x => xba (inl x)
      | inr yc => xba (inr (ycb yc))
      end).

  apply (MkIso
    (fun a =>
      match axb a with
      | inl x => inl x
      | inr b => inr (byc b)
      end)
    (fun xyc =>
      match xyc with
      | inl x => xba (inl x)
      | inr yc => xba (inr (ycb yc))
      end)); crush. Defined.

Lemma lens_prism_compose {A B C} (ab : Lens A B) (bc : Prism B C) : Affine A C.
Proof.
  destruct ab as [X ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y bc]. destruct bc as [byc ycb H1 H2].

  exists (pair (prod X Y) X); simpl.

  assert (A -> X * Y + X * C).
  refine
    (fun a =>
       match axb a with
       | (x, b) =>
         match byc b with
         | inl y => inl (pair x y)
         | inr c => inr (pair x c)
         end
       end).

  assert (X * Y + X * C -> A).
  refine
    (fun xyxc =>
      match xyxc with
      | inl (x, y) => xba (x, ycb (inl y))
      | inr (x, c) => xba (x, ycb (inr c))
      end).

  apply (MkIso
    (fun a =>
       match axb a with
       | (x, b) =>
         match byc b with
         | inl y => inl (pair x y)
         | inr c => inr (pair x c)
         end
       end)
    (fun xyxc =>
      match xyxc with
      | inl (x, y) => xba (x, ycb (inl y))
      | inr (x, c) => xba (x, ycb (inr c))
      end)); crush. Defined.

Lemma affine_compose {A B C} (ab : Affine A B) (bc : Affine B C) : Affine A C.
Proof.
  destruct ab as [XY ab]. destruct XY as [X Y]. destruct ab as [axyb xyba H H0].
  destruct bc as [UV bc]. destruct UV as [U V]. destruct bc as [buvc uvcb H1 H2].
  unfold IsInverse in *.
  simpl in *.
  exists (pair (sum X (prod Y U)) (prod Y V)); simpl.

  assert (A -> X + Y * U + Y * V * C).
  refine
    (fun a =>
      match axyb a with
      | inl x          => inl (inl x)
      | inr (pair y b) =>
        match buvc b with
        | inl u          => inl (inr (pair y u))
        | inr (pair v c) => inr (y, v, c)
        end
      end).

  assert (X + Y * U + Y * V * C -> A).
  refine
    (fun xyuvyc =>
       match xyuvyc with
       | inl (inl x)          => xyba (inl x)
       | inl (inr (pair y u)) => xyba (inr (pair y (uvcb (inl u))))
       | inr (y, v, c)        => xyba (inr (pair y (uvcb (inr (pair v c)))))
       end).

  apply (MkIso
    (fun a =>
      match axyb a with
      | inl x          => inl (inl x)
      | inr (pair y b) =>
        match buvc b with
        | inl u          => inl (inr (pair y u))
        | inr (pair v c) => inr (y, v, c)
        end
      end)
    (fun xyuvyc =>
       match xyuvyc with
       | inl (inl x)          => xyba (inl x)
       | inl (inr (pair y u)) => xyba (inr (pair y (uvcb (inl u))))
       | inr (y, v, c)        => xyba (inr (pair y (uvcb (inr (pair v c)))))
       end)); crush. Qed.

Definition affine_preview {A B} (affine : Affine A B) (a : A) : option B.
Proof.
  destruct affine as [XY ab]. destruct XY as [X Y]. destruct ab as [ayb bya _ _].
  destruct (ayb a) as [x | yb].
  - exact None.
  - exact (Some (snd yb)). Defined.

Definition affine_set {A B} (affine : Affine A B) (a : A) (b : B) : A.
Proof.
  destruct affine as [XY ab]. destruct XY as [X Y]. destruct ab as [ayb bya _ _].
  simpl in *.
  refine (match ayb a with
  | inl x          => bya (inl x)
  | inr (pair y _) => bya (inr (pair y b))
  end). Defined.

Definition option_const_map {A B} (a : A) (b : option B) : option A :=
  match b with
  | None   => None
  | Some _ => Some a
  end.

(* Is this right collection of laws? *)
Theorem affine_law1 {A B} (affine : Affine A B) :
  forall a b, affine_preview affine (affine_set affine a b) = option_const_map b (affine_preview affine a).
Proof.
  intros a b.
  destruct affine as [XY ab]. destruct ab as [ayb bya H H0]. simpl in *. destruct XY as [X Y]. simpl in *.
  remember (ayb a) as x. destruct x.
  - rewrite <- H0. reflexivity.
  - destruct p. rewrite <- H0. reflexivity. Qed.

Theorem affine_law2 {A B} (affine : Affine A B) :
  forall a b, affine_preview affine a = Some b -> affine_set affine a b = a.
Proof.
  intros a b Hsome.
  destruct affine as [XY ab]. destruct ab as [ayb bya H H0].
  crush. Qed.

Theorem affine_law3 {A B} (affine : Affine A B) :
  forall a b, affine_preview affine a = None -> affine_set affine a b = a.
Proof.
  intros a b Hsome.
  destruct affine as [XY ab]. destruct ab as [ayb bya H H0]. simpl in *. destruct XY as [X Y]. simpl in *.
  remember (ayb a) as x. destruct x.
  - crush.
  - inversion Hsome. Qed.

Theorem affine_law4 {A B} (affine : Affine A B) :
  forall a b b', affine_set affine (affine_set affine a b') b = affine_set affine a b.
Proof.
  intros a b b'.
  destruct affine as [XY ab]. destruct ab as [ayb bya H H0]. simpl. destruct XY as [X Y].
  destruct (ayb a); crush. Qed.

Theorem affine_complete {A B : Set} (preview : A -> option B) (set : A -> B -> A) :
  (forall a b, preview (set a b) = option_const_map b (preview a)) ->
  (forall a b, preview a = Some b -> set a b = a) ->
  (forall a b, preview a = None   -> set a b = a) ->
  (forall a b b', set (set a b) b' = set a b') ->
  Affine A B.
Proof.
  intros law1 law2 _ law4.

  set (X := { a : A | None = preview a }).
  set (Y := { ba : B -> A | exists (a : A), ba = set a /\ (exists (b : B), Some b = preview a) }). (* Maybe we need more here? *)

  exists (pair X Y). simpl.

  (*

  assert (FWD_test: A -> X + Y * B).
  refine (fun (a : A) =>
    let pa := preview a in
    let Heqpa := eq_refl : pa = preview a in
    (match pa as pa0 return (pa0 = preview a -> X + Y * B) with
      | None   => fun proof => inl (exist _ a proof)
      | Some b => fun proof => inr (pair (exist _ (set a) (ex_intro (fun x => set a = set x /\ (exists (b : B), Some b = preview x) ) a (conj eq_refl (ex_intro _ b proof)))) b)
      end) Heqpa).

  assert (BWD_test: X + Y * B -> A).
  refine (fun (p : X + Y * B) => match p with
    | inl (exist _ a _)           => a
    | inr (pair (exist _ ba _) b) => ba b
    end).

  *)

  set (FWD := fun (a : A) =>
    let pa := preview a in
    let Heqpa := eq_refl : pa = preview a in
    (match pa as pa0 return (pa0 = preview a -> X + Y * B) with
      | None   => fun proof => inl (exist _ a proof)
      | Some b => fun proof => inr (pair (exist _ (set a) (ex_intro (fun x => set a = set x /\ (exists (b : B), Some b = preview x) ) a (conj eq_refl (ex_intro _ b proof)))) b)
      end) Heqpa).

  set (BWD := (fun (p : X + Y * B) => match p with
    | inl (exist _ a _)           => a
    | inr (pair (exist _ ba _) b) => ba b
    end)).

  apply (MkIso FWD BWD); subst FWD; subst BWD.

  - intro a.
    set (Rw := dependentMatchOfMatch (fun o => o = preview a) A (preview a) eq_refl).
    rewrite Rw.
    clear Rw.
    remember (preview a) as pa. destruct pa.
    + symmetry. apply law2. symmetry. apply Heqpa.
    + reflexivity.
  - intro xyb. simpl. destruct xyb as [x | yb].
    + destruct x as [ a Hnone ].
      set (Lem2 := lem2_None (X + Y * B) (preview a)            Hnone). rewrite Lem2. reflexivity.
    + destruct yb as [ y b ]. destruct y as [ ba HBa]. destruct HBa as [a Hba]. destruct Hba as [Hba HSome]. destruct HSome as [b' HSome].
      rewrite Hba. clear Hba; clear ba.

      (* Helper statement using law1 *)
      assert (H : Some b = preview (set a b)).
      rewrite law1. rewrite <- HSome. simpl. reflexivity.

      set (Lem2 := lem2_Some (X + Y * B) (preview (set a b)) b H).      rewrite Lem2. clear Lem2.
      f_equal. f_equal.
      assert (set a = set (set a b)) as Hsetset.
      extensionality b0. symmetry. apply law4.
      apply sigma_eq with (eqp := Hsetset).
      apply proof_irrelevance. Qed.
