Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.
Require Import LensLaws.Lens.

Theorem lens_product {A B C} (ab : Lens A B) (ac : Lens A C)
  (law1 : forall a c, lens_view ab (lens_set ac a c) = lens_view ab a)
  (law2 : forall a b, lens_view ac (lens_set ab a b) = lens_view ac a)
  (law3 : forall a b c, lens_set ab (lens_set ac a c) b = lens_set ac (lens_set ab a b) c)
  : Lens A (B * C).
Proof.
  set (view := fun (a : A) => pair (lens_view ab a) (lens_view ac a)).
  set (set := fun (a : A) (bc : B * C) =>
    let (b, c) := bc in
    lens_set ac (lens_set ab a b) c).

  apply (@lens_complete _ _ view set); unfold view; unfold set.

  - intros a bc. destruct bc. f_equal.
    + rewrite law1. apply (lens_law1 ab).
    + rewrite <- law3. rewrite law2. apply (lens_law1 ac).

  - intros a. rewrite (lens_law2 ab). rewrite (lens_law2 ac). trivial.

  - intros a bc bc'. destruct bc as [b c]; destruct bc' as [b' c'].
    rewrite law3. rewrite (lens_law3 ac). rewrite (lens_law3 ab). trivial. Defined.
