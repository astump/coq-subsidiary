Require Import Init.
Require Import Initi.
Require Import Kinds.
Require Import Mu.
Require Import List.
Require Import Functors.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Require Import Coq.Logic.FunctionalExtensionality.


Import ListNotations.


Section Span.

  Variable A : Set.
  (* Bool equality *)
  Variable eqb : A -> A -> bool.
  (* propositional equality *)
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
    
  
  (* -------------------------------------------------------------------------------- *)
  (* Collect *)
  (* -------------------------------------------------------------------------------- *)

  Definition SpanF(X : Set) : Set := ((list A) * ListF A X).
  Global Instance SpanFunctor : Functor SpanF :=
    {fmap X Y f c :=
       let (l,r) := c in
         (l , fmap f r)
    }.
  
  Definition SpanAlg(p : A -> bool)(C : Set)
    : Alg (ListF A) C SpanF :=
    @rollAlg (ListF A) C SpanF
      (fun R reveal fo out eval xs => 
         match xs with
           Nil => (nil, xs)
         | Cons hd tl =>
            if p hd then
              let (l,r) := (eval tl) in
                (cons hd l, r)
            else
              (nil,xs)
         end).

  Definition span(p : A -> bool)(xs : List A) : (list A * List A)
    := let (l,r) := fold (ListF A) SpanF SpanFunctor (SpanAlg p (List A)) xs in
         (l,inL r).

  Definition spanl(p : A -> bool)(xs : list A) : (list A * list A) :=
    let (l,r) := span p (toList xs) in
      (l, fromList r).

End Span.

(* testcases *)

Definition test := spanl nat (eqb 1) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).

Eval compute in test.

