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

Section Repeat.

Variable A : Set.
Variable eqb : A -> A -> bool.

Lemma Repeat(p : A -> bool)(a : A) :
            p a = true ->
            forall(n : nat),
              spanr (fold (ListF A)) p (toList (repeat a n)) = (repeat a n, Nil).
  intro pa.
  induction n; trivial.
  + unfold spanr. simpl'. rewrite pa.
    unfold spanr , toList in IHn.
    rewrite IHn.
    trivial.
Qed.


End Repeat.
