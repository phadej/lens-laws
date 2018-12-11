Require Import LensLaws.Isomorphism.
Require Import LensLaws.These.
Require Import LensLaws.Functor.

Require Import Coq.Logic.ProofIrrelevance.

(* Way less powerful, and less magical then Adam Chipala's crush *)
Ltac crush := repeat (match goal with
  (* leaf tactics, concluding proofs. *)
  | [ |- ?x = ?x ] => reflexivity
  | [ H : ?P |- ?P ] => exact H

  (* unfold IsInverse in context and goal *)
  | [ H : IsInverse _ _ |- _ ] => unfold IsInverse in H
  | [ |- IsInverse _ _ ] => unfold IsInverse

  (* pair (fst a, snd a) = a *)
  | [ |- context[pair (fst ?a) (snd ?a)] ] => rewrite <- surjective_pairing

  (* construct pairs *)
  | [ |- pair _ _ ] => constructor
  (* introduce vars *)
  | [ |- _ -> _ ]   => intro

  (* destruct products, sums and units in the context *)
  | [ H : prod _ _  |- _ ] => destruct H
  | [ H : sum _ _   |- _ ] => destruct H
  | [ H : unit      |- _ ] => destruct H
  | [ H : option _  |- _ ] => destruct H
  | [ H : these _ _ |- _ ] => destruct H

  (* False facts *)
  | [ H : Empty_set |- _ ] => inversion H
  | [ H : None = Some _ |- _ ] => inversion H

  (* injective constructors, it's important to remove the hypothesis, otherwise will loop on it! *)
  | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H; subst

  (* if we match on function result, remember the result and destruct it *)
  | [ |- context[match ?f ?x with inl _ => _ | inr _ => _ end] ] =>
    let fx := fresh f x in remember (f x) as fx; destruct fx

  (* if we have inl x in the goal, but we remembered it's something else: rewrite *)
  | [ H : inl ?x = ?y |- context[inl ?x] ] => rewrite H
  | [ H : inr ?x = ?y |- context[inr ?x] ] => rewrite H

  (* similar match in context *)
  | [ H : context[match ?f ?x with inl _ => _ | inr _ => _ end] |- _ ] =>
    let fx := fresh f x in remember (f x) as fx; destruct fx

  (* if we match on function result, remember the result and destruct it *)
  | [ |- context[match ?f ?x with pair _ _ => _ end] ] =>
    let fx := fresh f x in remember (f x) as fx; destruct fx

  | [ H : (pair ?a ?b) = ?x |- context[pair ?a ?b] ] => rewrite H

  (* this matches on IsInverse hypothesis, and applies them *)
  | [ H : (forall (x : _), x = ?f (?g x)) |- context[?f (?g ?x)] ] => rewrite <- H
  end; simpl in *).


Lemma sigma_eq {A} {P : A -> Prop} (x y : A) (px : P x) (py : P y) (eqp : x = y) :
  (eq_ind x P px y eqp = py) ->
  exist P x px = exist P y py.
Proof.
  intros. subst. f_equal. Qed.

(* match of match (case of case) rewrite *)
Lemma matchOfMatch {A B O : Set} (P : Type) (opt : option O) (some : O -> A + B) (none : A + B) (f : A -> P) (g : B -> P)
  : match (match opt with
           | Some x => some x
           | None => none
           end) with
    | inl l => f l
    | inr r => g r
    end
  = match opt with
    | Some x =>
      match some x with
      | inl l => f l
      | inr r => g r
      end
    | None =>
      match none with
      | inl l => f l
      | inr r => g r
      end
    end.
Proof. destruct opt; reflexivity. Qed.

(* dependent match of match (case of case) rewrite *)
Lemma dependentMatchOfMatch {O : Set}
    (P : option O -> Type)
    (Q : Type)
    (opt : option O)
    (Popt : P opt)
    (A B : Set)
    (some : forall (o : O), P (Some o) -> A + B)
    (none : P None -> A + B)
    (f : A -> Q)
    (g : B -> Q)
  : match (match opt as pa return (P pa -> A + B) with
           | Some b => some b
           | None => none
           end Popt) with
    | inl l => f l
    | inr r => g r
    end
  = match opt as pa return (P pa -> Q) with
    | Some b => fun proof => match some b proof with inl l => f l | inr r => g r end
    | None   => fun proof => match none proof   with inl l => f l | inr r => g r end
    end Popt.
Proof.
  destruct opt; reflexivity. Qed.

Lemma lem2_Some {O : Set}
    (P : Type)
    (opt : option O)
    (x : O)
    (proof : Some x = opt)
    (f : forall (o : O), Some o = opt -> P)
    (g : None = opt -> P)
  : match opt as x0 return (x0 = opt -> P) with
    | Some b => fun pf : Some b = opt => f b pf
    | None => fun pf : None = opt => g pf
    end eq_refl
  = f x proof.
Proof.
  destruct opt.
  - inversion proof. subst. f_equal. apply proof_irrelevance.
  - inversion proof. Qed.

Lemma lem2_None {O : Set}
    (P : Type)
    (opt : option O)
    (proof : None = opt)
    (f : forall (o : O), Some o = opt -> P)
    (g : None = opt -> P)
  : match opt as x0 return (x0 = opt -> P) with
    | Some b => fun pf : Some b = opt => f b pf
    | None => fun pf : None = opt => g pf
    end eq_refl
  = g proof.
Proof.
  destruct opt.
  - inversion proof.
  - inversion proof. f_equal. apply proof_irrelevance. Qed.
