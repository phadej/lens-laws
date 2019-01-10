Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Functor.
Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.
Require Import LensLaws.Lens.

Require Import Coq.Logic.FunctionalExtensionality.

(* Setter *)
Definition Setter (A B : Set) : Type := { F : Set -> Set & IsFunctor F & Iso A (F B) }.

Lemma iso_is_setter {A B} (iso : Iso A B) : Setter A B.
Proof.
  destruct iso as [f g H H0].

  exists (fun X => X).
  - apply IdentityFunctor.
  - apply (MkIso f g); crush. Qed.

Lemma lens_is_setter {A B} (lens : Lens A B) : Setter A B.
  destruct lens as [X iso]. destruct iso as [f g H H0].

  exists (fun Y => prod X Y).
  - apply SndFunctor.
  - apply (MkIso f g); crush. Qed.

Lemma setter_compose {A B C} (ab : Setter A B) (bc : Setter B C) : Setter A C.
Proof.
  intros.
  destruct ab as [X XF ab]. destruct ab as [axb xba H H0].
  destruct bc as [Y YF bc]. destruct bc as [byc ycb H1 H2].

  exists (fun Z => X (Y Z)).
  - apply (ComposeFunctor XF YF).

  - destruct XF as [Xfmap Xid Xcomp]. destruct YF as [Yfmap Yid Ycomp].
    assert (Xcomp0: forall (A B C : Set) (f : A -> B) (g : B -> C) (xa : X A),
      Xfmap A C (fun a : A => g (f a)) xa = Xfmap B C g (Xfmap A B f xa)).
    intros U V W uv vw Xu. rewrite Xcomp. trivial.
    apply (MkIso
      (fun (a : A)         => Xfmap _ _ byc (axb a))
      (fun (xyc : X (Y C)) => xba (Xfmap _ _ ycb xyc))).
    + crush. rewrite <- Xcomp0. replace (fun a : B => ycb (byc a)) with (fun b : B => b).
      rewrite Xid. apply H. extensionality b. apply H1.
    + crush. rewrite <- Xcomp0. replace (fun yc : Y C => byc (ycb yc)) with (fun yc : Y C => yc).
      rewrite Xid. trivial. extensionality yc. apply H2. Defined.

Definition setter_over {A B} (setter : Setter A B) (bb : B -> B) (a : A) : A.
Proof.
  destruct setter as [F FF iso]. destruct FF as [fmap _ _]. destruct iso as [f g _ _].
  exact (g (fmap B B bb (f a))). Defined.

Theorem setter_law1 {A B} (setter : Setter A B) :
  forall a, setter_over setter (fun b : B => b) a = a.
Proof.
  intros a.
  destruct setter as [F FF iso]. destruct FF as [fmap Fid Fcomp]. destruct iso as [f g H0 H1].
  crush. rewrite Fid. symmetry. apply H0. Qed.

Theorem setter_law2 {A B} (setter : Setter A B) :
  forall a f g, setter_over setter (fun b : B => f (g b)) a = setter_over setter f (setter_over setter g a).
Proof.
  intros a u v.
  destruct setter as [F FF iso]. destruct FF as [fmap Fid Fcomp]. destruct iso as [f g H0 H1].
  crush.

  - assert (Xcomp0: forall (A B C : Set) (f : A -> B) (g : B -> C) (xa : F A),
      fmap A C (fun a : A => g (f a)) xa = fmap B C g (fmap A B f xa)).
    intros U V W uv vw Xu. rewrite Fcomp. trivial.

    rewrite <- Xcomp0. reflexivity. Qed.

Definition W (A B X : Set) : Set := (X -> B) -> A.
Instance Wfunctor {A B} : IsFunctor (W A B) :=
  { fmap := fun (X Y : Set) (xy : X -> Y) (wx : W A B X) =>
              fun yb => wx (fun x => yb (xy x)) }.
Proof.
  - intros Z. unfold W in *.
    extensionality w. extensionality yb. f_equal.
  - intros X Y Z f g. reflexivity. Qed.

Definition F {A B : Set} (over : (B -> B) -> (A -> A)) : Set -> Set :=
  fun (X : Set) => { f : W A B X | exists (a : A) (bx : B -> X), f = fun xb => over (fun b => xb (bx b)) a }.

Instance FunctorF {A B : Set} (over : (B -> B) -> (A -> A)) :
  IsFunctor (F over) :=
  {
     fmap X Y xy wx := match wx with
      | exist _ x e =>
         exist
          (fun f : W A B Y => exists (a : A) (bx : B -> Y),
                              f = (fun yb : Y -> B => over (fun b : B => yb (bx b)) a))
          (fun yb =>  x (fun x => yb (xy x)))
          (match e with
            | ex_intro _ a (ex_intro _ bx H) =>
              ex_intro _ a (ex_intro _ (fun b => xy (bx b))
                (match H in (_ = x') return
                  (fun yb : Y -> B => x (fun x0 : X => yb (xy x0))) =
                  (fun yb : Y -> B => x' (fun x0 : X => yb (xy x0)))
                with
                | eq_refl => eq_refl
                end))
            end)
     end
  }.
Proof.
  + intros Z. extensionality w. destruct w. f_equal.
    apply proof_irrelevance.
  + intros X Y Z f g. extensionality w. destruct w. f_equal.
    apply proof_irrelevance.
Qed.

Theorem setter_complete {A B : Set} (over : (B -> B) -> (A -> A)) :
  (forall a, over (fun b => b) a = a) ->
  (forall a f g, over (fun x => f (g x)) a = over f (over g a)) ->
  Setter A B.
Proof.
  intros law1 law2.

  exists (F over).
  apply (FunctorF over).

  - assert (FWD_test : A -> F over B).
    refine (fun (a : A) => exist
        (fun f : W A B B => exists (a : A) (bx : B -> B),
                        f = (fun yb : B -> B => over (fun b : B => yb (bx b)) a))
        (fun bb => over (fun b => bb b) a)
        (ex_intro _ a (ex_intro _ (fun b => b)
            eq_refl))).

    assert (BWD_test : F over B -> A).
    refine (fun (w : F over B) => match w with
    | exist _ wx _ => wx (fun (b : B) => b)
    end).

    apply (MkIso
      (fun (a : A) => exist
        (fun f : W A B B => exists (a : A) (bx : B -> B),
                        f = (fun yb : B -> B => over (fun b : B => yb (bx b)) a))
        (fun bb => over (fun b => bb b) a)
        (ex_intro _ a (ex_intro _ (fun b => b)
            eq_refl)))

      (fun (w : F over B) => match w with
        | exist _ wx _ => wx (fun (b : B) => b)
        end)).

    + intros a. symmetry. apply law1.
    + intros w. destruct w. destruct e. f_equal.
      assert (H : x = (fun bb : B -> B => over (fun b : B => bb b) (x (fun b : B => b)))).
        destruct e as [ bx e ].
        rewrite e.
        extensionality bb.
        rewrite <- law2. reflexivity.
      apply sigma_eq with (eqp := H).
      apply proof_irrelevance. Qed.
