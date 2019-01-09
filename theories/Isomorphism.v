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

Definition isoTo {A B} (iso : Iso A B) (a : A) : B :=
  match iso with
  | MkIso f _ _ _ => f a
  end.

Definition isoFrom {A B} (iso : Iso A B) (b : B) : A :=
  match iso with
  | MkIso _ g _ _ => g b
  end.

Theorem isoToFrom {A B} (iso : Iso A B) : forall (b : B),
    isoTo iso (isoFrom iso b) = b.
Proof.
  intros b.
  destruct iso as [fwd bwd H H'].
  unfold isoTo; unfold isoFrom.
  auto.
Qed.

Theorem isoFromTo {A B} (iso : Iso A B) : forall (a : A),
    isoFrom iso (isoTo iso a) = a.
Proof.
  intros a.
  destruct iso as [fwd bwd H H'].
  unfold isoTo; unfold isoFrom.
  auto.
Qed.
