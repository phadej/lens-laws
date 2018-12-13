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

Definition fun_id : Set -> Set := fun X => X.

Theorem IdentityFunctor : IsFunctor fun_id.
Proof.
  apply (MkFunctor (fun _ _ ab a => ab a)); reflexivity. Defined.

Definition fun_const (A : Set) : Set -> Set := fun X => A.

Theorem ConstFunctor (A : Set) : IsFunctor (fun_const A).
Proof.
  apply (@MkFunctor (fun_const A) (fun _ _ _ a => a)); reflexivity. Defined.

Definition fun_snd (A : Set) : Set -> Set := fun B => prod A B.

Theorem SndFunctor (A : Set) : IsFunctor (fun_snd A).
Proof.
  apply (MkFunctor (fun _ _ f xy => match xy with pair x y => pair x (f y) end)).
  - intros Y. extensionality xy. destruct xy. trivial.
  - intros U V W uv vw. extensionality xu. destruct xu. trivial. Defined.

Definition fun_comp (F G : Set -> Set) : Set -> Set := fun X => F (G X).

Theorem ComposeFunctor {F G : Set -> Set} (functorF : IsFunctor F) (functorG : IsFunctor G) : IsFunctor (fun_comp F G).
Proof.
  destruct functorF as [Ffmap Fid Fcomp].
  destruct functorG as [Gfmap Gid Gcomp].
  apply (MkFunctor (fun _ _ f => Ffmap _ _ (Gfmap _ _ f))).
  - intros A. rewrite Gid. rewrite Fid. trivial.
  - intros A B C f g. rewrite Gcomp. rewrite Fcomp. trivial. Defined.

Definition fun_prod (F G : Set -> Set) : Set -> Set := fun X => prod (F X) (G X).

Theorem ProductFunctor {F G : Set -> Set} (functorF : IsFunctor F) (functorG : IsFunctor G) : IsFunctor (fun_prod F G).
Proof.
  destruct functorF as [Fmap Fid Fcomp].
  destruct functorG as [Gmap Gid Gcomp].
  apply (@MkFunctor (fun_prod F G) (fun _ _ f p => let (x, y) := p in (Fmap _ _ f x, Gmap _ _ f y))).
  - intros. rewrite Fid. rewrite Gid. extensionality p. destruct p; trivial.
  - intros. rewrite Fcomp. rewrite Gcomp. extensionality p. destruct p; trivial. Qed.