Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.

Require Import LensLaws.Isomorphism.
Require Import LensLaws.Functor.
Require Import LensLaws.These.

Module LatticeLike.

Definition assoc {A B C : Set} : (A * B) * C -> A * (B * C) :=
  fun xyz => match xyz with
             | ((x,y),z) => (x,(y,z))
             end.

Definition swap {A B : Set} : (A * B) -> (B * A) :=
  fun xy => match xy with
            | (x,y) => (y, x)
            end.

Definition dup {A : Set} : A -> (A * A) :=
  fun x => (x,x).

Definition uncurry {A B C : Set} : (A -> B -> C) -> (A * B) -> C :=
  fun f ab => match ab with | (a,b) => f a b end.

Definition pair {A B C D : Set} : (A -> C) -> (B -> D) -> (A * B) -> (C * D) :=
  fun f g ab => match ab with | (a,b) => (f a, g b) end.

Definition pairT {A B C D : Set} : (A -> C) -> (B -> D) -> these A B -> these C D
  := fun f g xy =>
       match xy with
       | This x => This (f x)
       | That y => That (g y)
       | These x y => These (f x) (g y)
       end.

Definition assocT {A B C : Set} : these (these A B) C -> these A (these B C)
  := fun xyz =>
       match xyz with
       | This (This x) => This x
       | This (That y) => That (This y)
       | This (These x y) => These x (This y)
       | That z => That (That z)
       | These (This x) z => These x (That z)
       | These (That y) z => That (These y z)
       | These (These x y) z => These x (These y z)
       end.

Definition swapT {A B : Set} : these A B -> these B A
  := fun xy =>
       match xy with
       | This x => That x
       | That y => This y
       | These x y => These y x
       end.

Definition dupT {A : Set} : A -> these A A
  := fun x => These x x.

Definition fstT {A B : Set} : these A B -> option A
  := fun xy =>
       match xy with
       | This a => Some a
       | That _ => None
       | These a _ => Some a
       end.

Definition sndT {A B : Set} : these A B -> option B
  := fun xy => fstT (swapT xy).

Class IsZip {F : Set -> Set} `(FunF : IsFunctor F) :=
  {
    zip : forall {A B : Set}, F A -> F B -> F (prod A B);
    zip_naturality : forall {A B C D : Set}
                            (x : F A) (y : F B) (f : A -> C) (g : B -> D),
        zip (fmap f x) (fmap g y) = fmap (pair f g) (zip x y);
    zip_associativity :
      forall (A B C : Set) (x : F A) (y : F B) (z : F C),
        zip x (zip y z) = fmap assoc (zip (zip x y) z);
    zip_commutativity :
      forall (A B : Set) (x : F A) (y : F B),
        zip x y = fmap swap (zip y x);
    zip_idempotence :
      forall (A : Set) (x : F A),
        zip x x = fmap dup x;
  }.

Class IsAlign {F : Set -> Set} `(FF : IsFunctor F) :=
  {
    align : forall {A B : Set}, F A -> F B -> F (these A B);
    align_naturality : forall {A B C D : Set}
                            (x : F A) (y : F B) (f : A -> C) (g : B -> D),
        align (fmap f x) (fmap g y) = fmap (pairT f g) (align x y);
    align_associativity :
      forall (A B C : Set) (x : F A) (y : F B) (z : F C),
        align x (align y z) = fmap assocT (align (align x y) z);
    align_commutativity :
      forall (A B : Set) (x : F A) (y : F B),
        align x y = fmap swapT (align y x);
    align_idempotence :
      forall (A : Set) (x : F A),
        align x x = fmap dupT x;
  }.

Class IsLatticeLike {F : Set -> Set} `(FunF : IsFunctor F)
      `(! IsZip FunF) `(! IsAlign FunF) :=
  { zip_align_absorption : forall {A B : Set}
                                  (u : A * these A B -> A) (x : F A) (y : F B),
        (forall (a : A), u (a, This a) = a) ->
        (forall (a : A) (b : B), u (a, These a b) = a) ->
        fmap u (zip x (align x y)) = x;
    align_zip_absorption : forall {A B : Set}
                                  (u : these A (A * B) -> A) (x : F A) (y : F B),
        (forall (a : A), u (This a) = a) ->
        (forall (a : A) (b : B), u (These a (a,b)) = a) ->
        fmap u (align x (zip x y)) = x;
  }.

(** Utilities *)

Lemma zip_naturality_l {F : Set -> Set} `{zipF : IsZip F} :
  forall {A B C : Set} (x : F A) (y : F B) (f : A -> C),
    zip (fmap f x) y = fmap (pair f id) (zip x y).
Proof.
  intros A B C x y f.
  rewrite <- (fmap_id' y) at 1.
  apply zip_naturality.
Qed.

Lemma zip_naturality_r {F : Set -> Set} `{zipF : IsZip F} :
  forall {A B C : Set} (x : F A) (y : F B) (g : B -> C),
    zip x (fmap g y) = fmap (pair id g) (zip x y).
Proof.
  intros A B C x y f.
  rewrite <- (fmap_id' x) at 1.
  apply zip_naturality.
Qed.

Ltac use_zip_naturality :=
  rewrite ?zip_naturality, ?zip_naturality_l, ?zip_naturality_r;
  rewrite <- ?fmap_compose'.

Lemma align_naturality_l {F : Set -> Set} `{alignF : IsAlign F} :
  forall {A B C : Set} (x : F A) (y : F B) (f : A -> C),
    align (fmap f x) y = fmap (pairT f id) (align x y).
Proof.
  intros A B C x y f.
  rewrite <- (fmap_id' y) at 1.
  apply align_naturality.
Qed.

Lemma align_naturality_r {F : Set -> Set} `{alignF : IsAlign F} :
  forall {A B C : Set} (x : F A) (y : F B) (g : B -> C),
    align x (fmap g y) = fmap (pairT id g) (align x y).
Proof.
  intros A B C x y f.
  rewrite <- (fmap_id' x) at 1.
  apply align_naturality.
Qed.

Ltac use_align_naturality :=
  rewrite ?align_naturality, ?align_naturality_l, ?align_naturality_r;
  rewrite <- ?fmap_compose'.

(* old LatticeLike *)

Theorem zip_align_absorption_fst {F : Set -> Set} `{latticeF : IsLatticeLike F} :
  forall {A B : Set} (x : F A) (y : F B),
    fmap fst (zip x (align x y)) = x.
Proof.
  intros A B x y.
  apply zip_align_absorption; reflexivity.
Qed.

Theorem align_zip_absorption_fstT {F : Set -> Set} `{latticeF : IsLatticeLike F} :
  forall {A B : Set} (x : F A) (y : F B),
    fmap fstT (align x (zip x y)) = fmap Some x.
Proof.
  intros A B x y.
  set (joinOpt := fun (T : Set) (mmx : option (option T)) =>
                    match mmx with
                    | None => None
                    | Some None => None
                    | Some (Some x) => Some x
                    end).
  set (u := fun (T U : Set) (r : these (option T) (option T * U)) =>
              joinOpt T (fstT r)).
  set (ox := fmap Some x).
  assert (fmap fstT (align x (zip x y)) = fmap (u A B) (align ox (zip ox y)))
    as H.
  {
    unfold ox.
    rewrite zip_naturality_l.
    rewrite align_naturality.
    rewrite <- fmap_compose'.
    f_equal.
    extensionality aab.
    destruct aab as [a | [a' b] | a [a' b] ]; reflexivity.
  }
  rewrite H.
  apply align_zip_absorption.
  - intros [a|]; reflexivity.
  - intros [a|]; reflexivity.
Qed.

(* LatticeLike implies zip_idempotence and align_idempotence *)
Theorem lattice_to_zip_idempotence {F : Set -> Set} `{latticeF : IsLatticeLike F} :
  forall {A : Set} (x : F A),
    zip x x = fmap dup x.
Proof.
  intros A x.
  set (u := fun (tp : these A (A * A)) =>
              match tp with
              | This a => a
              | That (a,_) => a
              | These a _ => a
              end).
  set (v := fun (pt : (A * A) * these (A * A) (A * A)) =>
              match pt with
              | ((a,_), This (_,a')) => (a, a')
              | ((a,_), That (a',_)) => (a, a')
              | ((a,_), These (_,a') _) => (a, a')
              end).
  assert (x = fmap u (align x (zip x x))) as A1.
  {
    symmetry.
    apply align_zip_absorption; reflexivity.
  }
  rewrite A1 at 2.
  rewrite zip_naturality_r.
  assert (pair id u = fun pt => v (pair dup (pairT dup id) pt)) as A2.
  {
    extensionality pt.
    destruct pt as [a1 [a2 | [a3 a4] | a2 [a3 a4]]]; reflexivity.
  }
  rewrite A2.
  rewrite fmap_compose.
  rewrite <- zip_naturality.
  rewrite <- align_naturality.
  rewrite fmap_id.
  apply zip_align_absorption.
  - intros [a1 a2].
    reflexivity.
  - intros [a1 a2] [a3 a4].
    reflexivity.
Qed.

Lemma lattice_to_align_idempotence_pre
      {F : Set -> Set}
      `{latticeF : IsLatticeLike F} :
  forall {A : Set} (x : F A),
    fmap fstT (align x x) = fmap Some x.
Proof.
  intros A x.
  assert (x = fmap fst (zip x (align x x))) as A1.
  {
    symmetry.
    apply zip_align_absorption; reflexivity.
  }
  rewrite A1 at 2.
  rewrite align_naturality_r.
  rewrite <- fmap_compose'.
  assert ((fun a : these A (A * these A A) => fstT (pairT id fst a)) = fstT) as A2.
  {
    extensionality tp.
    destruct tp as [l | r | l r]; reflexivity.
  }
  rewrite A2.
  apply align_zip_absorption_fstT.
Qed.

Lemma repair_these:
  forall (A B : Set),
  (fun (ab : these A B) => toThese (fstT ab) (sndT ab)) = Some.
Proof.
  intros A B.
  extensionality ab.
  destruct ab as [a | b | a b]; reflexivity.
Qed.

Lemma fmap_product {F : Set -> Set} `{functorF : IsFunctor F} :
  forall (A B : Set)
         (x : F (prod A B)) (y : F (prod A B)),
    fmap fst x = fmap fst y ->
    fmap snd x = fmap snd y ->
    x = y.
Proof.
Admitted.

Lemma fmap_injective {F : Set -> Set} `{functorF : IsFunctor F} :
  forall (A B : Set)
         (f : A -> B),
    (forall a1 a2, f a1 = f a2 -> a1 = a2) ->
    (forall x y, fmap f x = fmap f y -> x = y).
Proof.
Admitted.

Lemma fmap_product' {F : Set -> Set} `{functorF : IsFunctor F} :
  forall (A A' B C D : Set)
         (f : A -> B) (f' : A' -> B)
         (g : A -> C) (g' : A' -> C)
         (h : B -> C -> D)
         (x : F A) (y : F A'),
    fmap f x = fmap f' y ->
    fmap g x = fmap g' y ->
    fmap (fun a => h (f a) (g a)) x = fmap (fun a' => h (f' a') (g' a')) y.
Proof.
  intros A A' B C D f f' g g' h x y.
  intros Hf Hg.
  assert (fmap (fun a => h (f a) (g a)) x =
          fmap (uncurry h) (fmap (fun a => (f a, g a)) x)) as A1.
  {
    rewrite <- fmap_compose'.
    reflexivity.
  }
  assert (fmap (fun a' => h (f' a') (g' a')) y =
          fmap (uncurry h) (fmap (fun a' => (f' a', g' a')) y)) as A2.
  {
    rewrite <- fmap_compose'.
    reflexivity.
  }
  rewrite A1.
  rewrite A2.
  f_equal.
  apply fmap_product.
  - rewrite <- !fmap_compose'.
    apply Hf.
  - rewrite <- !fmap_compose'.
    apply Hg.
Qed.

Theorem lattice_to_align_idempotence
        {F : Set -> Set}
        `{latticeF : IsLatticeLike F} :
  forall {A : Set} (x : F A),
    align x x = fmap dupT x.
Proof.
  intros A x.
  assert (fmap fstT (align x x) = fmap Some x)
    as A1
      by apply lattice_to_align_idempotence_pre.
  assert (fmap sndT (align x x) = fmap Some x)
    as A2.
  {
    unfold sndT.
    rewrite fmap_compose.
    rewrite <- align_commutativity.
    exact A1.
  }
  assert (fmap Some (align x x) = fmap Some (fmap dupT x)) as A3.
  {
    rewrite <- repair_these at 1.
    rewrite (fmap_product' toThese A1 A2).
    rewrite <- fmap_compose'.
    f_equal.
  }
  apply (@fmap_injective _ _ _ _ Some).
  - intros a1 a2 I.
    inversion I.
    reflexivity.
  - exact A3.
Qed.

(** Identity *)

Instance IdentityZip : IsZip IdentityFunctor := {}.
Proof.
  (* zip *)
  - intros A B.
    exact (fun a => fun b => (a,b)).
  (* zip_naturality, zip_associativity,
     zip_commutativity, zip_idempotence *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Instance IdentityAlign : IsAlign IdentityFunctor := {}.
Proof.
  (* align *)
  - unfold Identity.
    intros A B.
    apply These.
  (* align_naturality, align_associativity,
     align_commutativity, align_idempotence *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Instance IdentityLatticeLike : IsLatticeLike IdentityZip IdentityAlign := {}.
Proof.
  - intros A B u x y H1 H2.
    simpl.
    apply H2.
  - intros A B u x y H1 H2.
    simpl.
    apply H2.
Defined.

(** Option *)

Instance OptionZip : IsZip OptionFunctor := {}.
Proof.
  (* zip *)
  - intros A B ma mb.
    exact (
        match ma with
        | None   => None
        | Some a => match mb with
                    | None   => None
                    | Some b => Some (a,b)
                    end
        end
      ).
  (* zip_naturality *)
  - intros A B C D mx my f g.
    simpl.
    destruct mx; destruct my; reflexivity.
  (* zip_associativity *)
  - intros A B C mx my mz.
    simpl.
    destruct mx; destruct my; destruct mz; reflexivity.
  (* zip_commutativity *)
  - intros A B mx my.
    simpl.
    destruct mx; destruct my; reflexivity.
  (* zip_idempotence *)
  - intros A mx.
    simpl.
    destruct mx; reflexivity.
Defined.

Instance OptionAlign : IsAlign OptionFunctor := {}.
Proof.
  (* align *)
  - exact (
    fun {A B : Set} (ma : option A) (mb : option B) =>
        match ma with
        | None => match mb with
                  | None => None
                  | Some b => Some (That b)
                  end
        | Some a => match mb with
                    | None => Some (This a)
                    | Some b => Some (These a b)
                    end
        end).
  - intros A B C D ma mb f g.
    destruct ma, mb; reflexivity.
  - intros A B C ma mb mc.
    destruct ma, mb, mc; reflexivity.
  - intros A B ma mb.
    destruct ma, mb; reflexivity.
  - intros A ma.
    destruct ma; reflexivity.
Defined.

Instance OptionLatticeLike : IsLatticeLike OptionZip OptionAlign := {}.
Proof.
  - intros A B u ma mb H1 H2.
    destruct ma; destruct mb; simpl; congruence.
  - intros A B u ma mb H1 H2.
    destruct ma; destruct mb; simpl; congruence.
Defined.

(** Product *)

Instance ProductZip {F G : Set -> Set}
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `(! IsZip FunF) `(! IsZip FunG) :
  IsZip (ProductFunctor FunF FunG):= {}.
Proof.
  (* zip *)
  - intros A B x y.
    destruct x as [fx gx].
    destruct y as [fy gy].
    exact (zip fx fy, zip gx gy).
  (* zip_naturality *)
  - intros A B C X [fx gx] [fy gy] f g.
    simpl.
    use_zip_naturality.
    reflexivity.
  (* zip_associativity *)
  - intros A B C [fx gx] [fy gy] [fz gz].
    simpl.
    rewrite zip_associativity.
    rewrite zip_associativity.
    reflexivity.
  (* zip_commutativity *)
  - intros A B [fx gx] [fy gy].
    simpl.
    rewrite zip_commutativity.
    rewrite (zip_commutativity gx gy).
    reflexivity.
  (* zip_idempotence *)
  - intros A [fx gx].
    simpl.
    rewrite zip_idempotence.
    rewrite zip_idempotence.
    reflexivity.
Defined.

Instance ProductAlign {F G : Set -> Set} 
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `(! IsAlign FunF) `(! IsAlign FunG) :
  IsAlign (ProductFunctor FunF FunG) := {}.
Proof.
  (* align *)
  - intros A B [fa ga] [fb gb].
    exact (align fa fb, align ga gb).
  (* laws *)
  - intros A B C D [fa ga] [fb gb] f g.
    simpl.
    rewrite align_naturality.
    rewrite align_naturality.
    reflexivity.
  - intros A B C [fa ga] [fb gb] [fc gc].
    simpl.
    rewrite align_associativity.
    rewrite align_associativity.
    reflexivity.
  - intros A B [fa ga] [fb gb].
    simpl.
    rewrite <- align_commutativity.
    rewrite <- align_commutativity.
    reflexivity.
  - intros A [fa ga].
    simpl.
    rewrite align_idempotence.
    rewrite align_idempotence.
    reflexivity.
Defined.

Instance ProductLatticeLike {F G : Set -> Set}
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `{ZipF : ! IsZip FunF, ZipG : ! IsZip FunG}
         `{AlignF : ! IsAlign FunF, AlignG : ! IsAlign FunG}
         `(! IsLatticeLike ZipF AlignF, ! IsLatticeLike ZipG AlignG) :
  IsLatticeLike (ProductZip ZipF ZipG) (ProductAlign AlignF AlignG) := {}.
Proof.
  - intros A B u [fa ga] [fb gb] H1 H2.
    simpl.
    rewrite zip_align_absorption.
    rewrite zip_align_absorption.
    reflexivity.
    exact H1. exact H2.
    exact H1. exact H2.
  - intros A B u [fa ga] [fb gb] H1 H2.
    simpl.
    rewrite align_zip_absorption.
    rewrite align_zip_absorption.
    reflexivity.
    exact H1. exact H2.
    exact H1. exact H2.
Defined.

(** Compose *)

Instance ComposeZip {F G : Set -> Set}
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `(! IsZip FunF) `(! IsZip FunG) :
  IsZip (ComposeFunctor FunF FunG) := {}.
Proof.
  (* zip *)
  - intros A B x y.
    exact (fmap (uncurry zip) (zip x y)).
  (* zip_naturality *)
  - intros A B C D x y f g.
    simpl.
    use_zip_naturality.
    f_equal.
    extensionality a.
    destruct a as [ga gb].
    simpl.
    use_zip_naturality.
    reflexivity.
  (* zip_associativity *)
  - intros A B C x y z.
    simpl.
    use_zip_naturality.
    rewrite zip_associativity.
    rewrite <- ?fmap_compose'.
    f_equal.
    extensionality ga_gb_gc.
    destruct ga_gb_gc as [[ga gb] gc].
    unfold uncurry, assoc, pair.
    apply zip_associativity.
  (* zip_commutativity *)
  - intros A B x y.
    simpl.
    rewrite zip_commutativity.
    rewrite <- ?fmap_compose'.
    f_equal.
    extensionality gb_ga.
    destruct gb_ga as [gb ga].
    unfold uncurry, swap.
    apply zip_commutativity.
  (* zip_idempotence *)
  - intros A x.
    simpl.
    rewrite zip_idempotence.
    rewrite <- fmap_compose'.
    f_equal.
    extensionality ga.
    unfold uncurry, dup.
    apply zip_idempotence.
Defined.

Definition unwrap_these {F : Set -> Set} `{AlignF : IsAlign F} {A B : Set} :
  these (F A) (F B) -> F (these A B) :=
  fun t_fa_fb =>
    match t_fa_fb with
    | This fa => fmap This fa
    | That fb => fmap That fb
    | These fa fb => align fa fb
    end.

Instance ComposeAlign {F G : Set -> Set} 
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `(! IsAlign FunF) `(! IsAlign FunG) :
  IsAlign (ComposeFunctor FunF FunG) := {}.
Proof.
  - intros A B fga fgb.
    exact (fmap unwrap_these (align fga fgb)).
  - intros A B C D fga fgb f g.
    simpl.
    rewrite align_naturality.
    rewrite <- ? fmap_compose'.
    f_equal.
    extensionality t_ga_gb.
    destruct t_ga_gb as [ga|gb|ga gb].
    + simpl.
      rewrite <- ? fmap_compose'.
      reflexivity.
    + simpl.
      rewrite <- ? fmap_compose'.
      reflexivity.
    + simpl.
      apply align_naturality.
  - intros A B C fga fgb fgc.
    simpl.
    use_align_naturality.
    rewrite align_associativity.
    rewrite <- ? fmap_compose'.
    f_equal.
    extensionality abc.
    destruct abc as [[ga|gb|ga gb] | gc | [ga|gb|ga gb] gc];
      simpl;
      rewrite <- ? fmap_compose';
      try reflexivity.
    + use_align_naturality.
      reflexivity.
    + use_align_naturality.
      f_equal.
      extensionality a.
      destruct a; reflexivity.
    + use_align_naturality.
      f_equal.
      extensionality a.
      destruct a; reflexivity.
    + rewrite align_associativity.
      reflexivity.
  - intros A B fga fgb.
    simpl.
    rewrite align_commutativity.
    rewrite <- ? fmap_compose'.
    f_equal.
    extensionality gb_ga.
    destruct gb_ga as [gb|ga|gb ga]; simpl.
    + rewrite <- fmap_compose'.
      reflexivity.
    + rewrite <- fmap_compose'.
      reflexivity.
    + rewrite align_commutativity.
      reflexivity.
  - intros A x.
    simpl.
    rewrite align_idempotence.
    rewrite <- ? fmap_compose'.
    f_equal.
    extensionality a.
    simpl.
    rewrite align_idempotence.
    reflexivity.
Defined.

Instance ComposeLatticeLike {F G : Set -> Set}
         `{FunF : IsFunctor F, FunG : IsFunctor G}
         `{ZipF : ! IsZip FunF, ZipG : ! IsZip FunG}
         `{AlignF : ! IsAlign FunF, AlignG : ! IsAlign FunG}
         `(! IsLatticeLike ZipF AlignF, ! IsLatticeLike ZipG AlignG) :
  IsLatticeLike (ComposeZip ZipF ZipG) (ComposeAlign AlignF AlignG) := {}.
Proof.
  - intros A B u fga fgb H1 H2.
    simpl.
    rewrite zip_naturality_r.
    rewrite <- !fmap_compose'.
    apply zip_align_absorption; simpl.
    + intros ga.
      rewrite zip_naturality_r.
      rewrite zip_idempotence.
      rewrite <- !fmap_compose'.
      simpl.
      unfold id.
      rewrite <- fmap_id'.
      f_equal.
      extensionality a.
      apply H1.
    + intros ga gb.
      unfold id.
      apply zip_align_absorption.
      exact H1.
      exact H2.
  - intros A B u fga fgb H1 H2.
    simpl.
    rewrite align_naturality_r.
    rewrite <- !fmap_compose'.
    apply align_zip_absorption; simpl.
    + intros ga.
      rewrite <- fmap_compose'.
      rewrite <- fmap_id'.
      f_equal.
      extensionality a.
      apply H1.
    + intros ga gb.
      unfold id.
      apply align_zip_absorption.
      exact H1.
      exact H2.
Defined.
 

End LatticeLike.
