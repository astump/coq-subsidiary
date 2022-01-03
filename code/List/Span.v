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
    
  Inductive SpanF(X : Set) : Set :=
    SpanNoMatch : SpanF X
  | SpanSomeMatch : list A -> X -> SpanF X.

  Arguments SpanNoMatch{X}.
  Arguments SpanSomeMatch{X}.

  Global Instance SpanFunctor : Functor (@SpanF) :=
    {fmap X Y f c :=
       match c with
         SpanNoMatch => SpanNoMatch 
       | SpanSomeMatch l x => SpanSomeMatch l (f x)
       end
    }.
  
  Definition SpanAlg(p : A -> bool)(C : Set)
    : Alg (ListF A) C (@SpanF) :=
    rollAlg 
      (fun R reveal fo out eval xs => 
         match xs with
           Nil => SpanNoMatch 
         | Cons hd tl =>
            if p hd then
              match (eval tl) with
                SpanNoMatch => SpanSomeMatch [hd] tl
              | SpanSomeMatch l r => SpanSomeMatch (hd::l) r
              end
            else
              SpanNoMatch
         end).

  Definition spanr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                  (p : A -> bool)(xs : R) : SpanF R
    := fo SpanF SpanFunctor (SpanAlg p R) xs.

  Definition span(p : A -> bool)(xs : List A) : SpanF (List A)
    := fold (ListF A) SpanF SpanFunctor (SpanAlg p (List A)) xs.

  Definition spanl(p : A -> bool)(xs : list A) : SpanF (list A) :=
    fmap fromList (span p (toList xs)).

End Span.

Arguments spanr{A}{R}fo p xs.
Arguments span{A} p xs.
Arguments SpanNoMatch{A}{X}.
Arguments SpanSomeMatch{A}{X}.

(*Ltac foldSpan :=
  change (fold (ListF ?A) (SpanF ?A) (SpanFunctor ?A) (SpanAlg ?A ?p (List ?A)) ?t) with (span ?A ?p ?t). 
*)

(* testcases *)

Definition test := spanl nat (eqb 1) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test2 := spanl nat (eqb 0) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).

Eval compute in test.
Eval compute in test2.

