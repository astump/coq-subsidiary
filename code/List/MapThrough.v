(* similar to repeatedly from Haskell's Data.List.Extra, as an Alg *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Definition mappedT(A B : Set) : Set :=
  forall(R : Set)(fo:FoldT (Alg (ListF A)) R),
    A -> R -> B * R.

Section MapThrough.

  Context {A : Set}(eqb : A -> A -> bool).

  Definition MapThroughAlg
             {B : Set}
             (mapped:mappedT A B)
             (C : Set) : Alg (ListF A) C (Const (List B)) :=
    rollAlg 
      (fun R reveal fo eval xs => 
         match xs with
           Nil => mkNil 
         | Cons hd tl =>
           let (b,c) := mapped R fo hd tl in
             mkCons b (eval c)
         end).

  Definition mapThroughr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                        (B : Set)(mapped:mappedT A B)
                   : R -> List B :=
    fo (Const (List B)) (FunConst (List B)) (MapThroughAlg mapped R).

  Definition mapThrough(B : Set)(mapped:mappedT A B)
                   : List A -> List B :=
    mapThroughr (fold (ListF A)) B mapped.

End MapThrough.

