(* similar to span from Haskell's Data.List, but written as an Alg *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Span.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
    
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

  Definition spanr(R : Set)(fo:FoldT (Alg (ListF A)) R)
                 (p : A -> bool)(xs : R) : (list A * ListF A R)
    := fo SpanF SpanFunctor (SpanAlg p R) xs.

  Definition span(p : A -> bool)(xs : List A) : (list A * ListF A (List A))
    := fold (ListF A) SpanF SpanFunctor (SpanAlg p (List A)) xs.

  Definition spanl(p : A -> bool)(xs : list A) : (list A * list A) :=
    let (l,r) := span p (toList xs) in
      (l, fromList (inList r)).

End Span.

(* testcases *)

Definition test := spanl nat (eqb 1) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).

Eval compute in test.

