Definition IsInverse {A : Set} {B : Set} (f : A -> B) (g : B -> A) : Prop :=
  forall x, x = g (f x).

Inductive Iso (A B : Set) : Set :=
  MkIso :
    forall (f : A -> B),
    forall (g : B -> A),
    IsInverse f g ->
    IsInverse g f ->
    Iso A B.

Arguments MkIso {A} {B} f g fg gf.
