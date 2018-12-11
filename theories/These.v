Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive these (A B : Set) : Set :=
  | This  : A -> these A B
  | That  : B -> these A B
  | These : A -> B -> these A B.

Arguments This {_} {_} x.
Arguments That {_} {_} y.
Arguments These {_} {_} x y.

Definition toThese {A B : Set} (x : option A) (y : option B) : option (these A B) :=
  match (x, y) with
  | (None, None)     => None
  | (Some x, None)   => Some (This x)
  | (None, Some y)   => Some (That y)
  | (Some x, Some y) => Some (These x y)
  end.
