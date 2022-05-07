(* substitute a number and a wordsBy function for the capitalized names *)
Require Import WordsByWf.
Require Import WordsBy.
Require Import WordsByPath.

Require Import Lists.List.

Definition t1 := repeat 1 NUM.
Definition t2 := repeat 0 NUM.

Eval compute in (length (WORDSBY (Nat.eqb 0) (t1 ++ t2 ++ t1 ++ t2))).

(* 
Definition t1 := repeat 1 NUM.

Eval compute in (WORDSBY (Nat.eqb 0) (1 :: 1 :: 2 :: (t1 ++ 1 :: 3 :: 5 :: 0 :: nil))).

*)