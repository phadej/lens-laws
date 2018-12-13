Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Crush.
Require Import LensLaws.Prism.

Theorem prism_sum {A B C} (ab : Prism A B) (ac : Prism A C)
  (law1 : forall c, prism_preview ab (prism_review ac c) = None)
  (law2 : forall b, prism_preview ac (prism_review ab b) = None)
  : Prism A (B + C).
Proof.
  set (review := fun (bc : B + C) => match bc with
    | inl b => prism_review ab b
    | inr c => prism_review ac c
    end).

  set (preview := fun (a : A) => match prism_preview ab a with
    | Some b => Some (inl b)
    | None   => match prism_preview ac a with
      | Some c => Some (inr c)
      | None   => None
      end
    end).

  apply (@prism_complete _ _ review preview); unfold review; unfold preview.

  - intros bc. destruct bc.
    + rewrite (prism_law1 ab). reflexivity.
    + rewrite law1. rewrite (prism_law1 ac). reflexivity.

  - intros a bc. destruct bc.
    + remember (prism_preview ab a) as pa. destruct pa; crush.
      * apply prism_law2. symmetry. apply Heqpa.
      * remember (prism_preview ac a) as pc. destruct pc; crush.

    + remember (prism_preview ab a) as pa. destruct pa; crush.
      remember (prism_preview ac a) as pc. destruct pc; crush.
      apply prism_law2. symmetry. apply Heqpc. Qed.
    