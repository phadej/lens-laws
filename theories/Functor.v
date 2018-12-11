Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

(* Functor *)
Inductive IsFunctor (F : Set -> Set) : Type :=
  MkFunctor :
    forall (fmap : (forall {A B : Set}, (A -> B) -> F A -> F B)),
    (forall (A : Set), fmap (fun (x : A) => x) = (fun fx => fx)) ->
    (forall (A B C : Set) (f : A -> B) (g : B -> C), (fmap (fun a => g (f a)) = (fun fa => fmap g (fmap f fa)))) ->
    IsFunctor F.

Arguments MkFunctor {_} fmap fid fcompose : rename.

Theorem IdentityFunctor : IsFunctor (fun A => A).
Proof.
  apply (MkFunctor (fun _ _ ab a => ab a)); reflexivity. Defined.

Theorem SndFunctor {A : Set} : IsFunctor (fun B => prod A B).
Proof.
  apply (MkFunctor (fun _ _ f xy => match xy with pair x y => pair x (f y) end)).
  - intros Y. extensionality xy. destruct xy. trivial.
  - intros U V W uv vw. extensionality xu. destruct xu. trivial. Defined.

Theorem ComposeFunctor {F G : Set -> Set} (functorF : IsFunctor F) (functorG : IsFunctor G) : IsFunctor (fun X => F (G X)).
Proof.
  destruct functorF as [Ffmap Fid Fcomp].
  destruct functorG as [Gfmap Gid Gcomp].
  apply (MkFunctor (fun _ _ f => Ffmap _ _ (Gfmap _ _ f))).
  - intros A. rewrite Gid. rewrite Fid. trivial.
  - intros A B C f g. rewrite Gcomp. rewrite Fcomp. trivial. Defined.
