(* prove that repeating an element satisfying p 
   gives you (from span) the pair of that same repetition and Nil *) 

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import List.Span.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Require Import List.Repeat.

Section Repeat.

Variable A : Set.
Variable eqb : A -> A -> bool.

Lemma Repeat(p : A -> bool)(a : A) :
            p a = true ->
            forall(n : nat),
              span A p (toList (repeat n a)) = (repeat n a, Nil).
  intro pa.
  induction n.
  ++ reflexivity.
  ++ simpl'; rewrite pa.
     unfold span , toList in IHn.
     rewrite IHn.
     reflexivity.
Qed.


End Repeat.
