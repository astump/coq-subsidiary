(* similar to wordsBy from Haskell's Data.List.Extra *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import Span.

Import ListNotations.

Section WordsBy.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
  
  Definition WordsBy(p : A -> bool)(C : Set)
    : Alg (ListF A) C (Const (list (list A))) :=
    rollAlg 
      (fun R reveal fo wordsBy xs => 
         match xs with
           Nil => [] 
         | Cons hd tl =>
           if p hd then
             wordsBy tl
           else
             let (w,z) := breakr fo p tl in
             (hd :: w) :: wordsBy z
         end).

  Definition wordsByr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                     (p : A -> bool)(xs : R) : list (list A) :=
    fo (Const (list (list A))) (FunConst (list (list A))) (WordsBy p R) xs.

  Definition wordsBy(p : A -> bool)(xs : List A) : list (list A) :=
    wordsByr (fold (ListF A)) p xs.

End WordsBy.

Arguments wordsByr{A}{R}fo p xs.
Arguments wordsBy{A} p xs.

(* testcases *)

(* 0 will play the role of a space *)
Definition test := wordsBy (eqb 0) (toList (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: [])).

Eval compute in test.


