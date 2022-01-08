(* similar to wordsBy from Haskell's Data.List.Extra *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import SplitAt.
Require Import MapThrough.

Import ListNotations.

Section ChunksOf.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
  
  (* this assumes that s is the predecessor of the desired chunk size *)
  Definition ChunksOf(s : nat)(C : Set)
    : Alg (ListF A) C (Const (List (list A))) :=
    MapThroughAlg (fun R fo hd tl => let (l,r) := splitAtr fo s tl in (hd :: l, r)) C.

  Definition chunksOfr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                      (s : nat)(xs : R) : List (list A) :=
    match s with
      O => mkNil
    | S n =>
      fo (Const (List (list A))) (FunConst (List (list A))) (ChunksOf n R) xs
    end.

  Definition chunksOf : nat -> List A -> List (list A) :=
    chunksOfr (fold (ListF A)).

  Definition chunksOfl(s : nat)(l : list A) : list (list A) :=
    fromList (chunksOfr (fold (ListF A)) s (toList l)).

End ChunksOf.

Arguments chunksOfr{A}{R}.
Arguments chunksOf{A}{R}.
Arguments chunksOfl{A}.

(* testcases *)

Definition test := chunksOfl 0 (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: []).
Definition test2 := chunksOfl 3 (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: []).

Eval compute in test.
Eval compute in test2.


