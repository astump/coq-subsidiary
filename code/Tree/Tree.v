Require Import Functors.
Require Import Subrec.
Require Import Coq.Lists.List.

Section Tree.

Variable A : Set.

Inductive TreeF(X : Set) :=
  Leaf : A -> TreeF X
| Branch : list X -> TreeF X.

Definition Tree := Subrec TreeF.

Definition MirrorAlg : Alg TreeF Tree (Const Tree) :=
  rollAlg
    (fun R reveal fold eval d =>
       match d with
         Leaf a => Leaf a
       | .