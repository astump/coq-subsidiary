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

  Global Instance SpanFunctor : Functor SpanF :=
    {fmap X Y f c :=
       match c with
         SpanNoMatch => SpanNoMatch 
       | SpanSomeMatch l x => SpanSomeMatch l (f x)
       end
    }.
  
  Lemma SpanFunctorId : FmapId SpanF SpanFunctor.
    intros B d.
    destruct d; trivial.
  Qed.

  Definition SpanAlg(p : A -> bool)
    : Alg (ListF A) SpanF :=
    rollAlg 
      (fun R fo span xs => 
         match xs with
           Nil => SpanNoMatch 
         | Cons hd tl =>
            if p hd then
              match (span tl) with
                SpanNoMatch => SpanSomeMatch [hd] tl
              | SpanSomeMatch l r => SpanSomeMatch (hd::l) r
              end
            else
              SpanNoMatch 
         end).

  Definition spanhr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                  (p : A -> bool)(xs : R) : SpanF R :=
    fo SpanF SpanFunctor (SpanAlg p) xs.

  Definition spanh(p : A -> bool)(xs : List A) : SpanF (List A) :=
    spanhr (fold (ListF A)) p xs.

  Definition spanr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                  (p : A -> bool)(xs : R) : list A * R
    := match spanhr fo p xs with
         SpanNoMatch => ([],xs)
       | SpanSomeMatch l r => (l,r)
       end.

  Definition span(p : A -> bool)(xs : List A) : list A * List A
    := spanr (fold (ListF A)) p xs.

  (* intended just for testing below *)
  Definition spanl(p : A -> bool)(xs : list A) : list A * list A :=
    let (l,r) := span p (toList xs) in
      (l,fromList r).

  Definition dropWhiler{R : Set}(fo:FoldT (Alg (ListF A)) R)
             (p : A -> bool)(xs : R) : R :=
    snd (spanr fo p xs).

  Definition dropWhile(p : A -> bool)(xs : List A) : List A :=
    dropWhiler (fold (ListF A)) p xs.

  Definition breakr{R : Set}(fo:FoldT (Alg (ListF A)) R)
             (p : A -> bool)(xs : R) : list A * R :=
    (spanr fo (fun x => negb (p x)) xs).

  Definition break(p : A -> bool)(xs : List A) : list A * List A :=
    breakr (fold (ListF A)) p xs.

End Span.

Arguments spanr{A}{R}fo p xs.
Arguments span{A} p xs.
Arguments spanh{A} p xs.
Arguments spanhr{A}{R}fo p xs.
Arguments SpanNoMatch{A}{X}.
Arguments SpanSomeMatch{A}{X}.
Arguments dropWhiler{A}{R}.
Arguments dropWhile{A}.
Arguments breakr{A}{R}.
Arguments break{A}.

(*Ltac foldSpan :=
  change (fold (ListF ?A) (SpanF ?A) (SpanFunctor ?A) (SpanAlg ?A ?p (List ?A)) ?t) with (span ?A ?p ?t). 
*)

(* testcases *)

Definition test := spanl nat (eqb 1) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test2 := spanl nat (eqb 0) (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test3 := spanl nat (eqb 0) (0 :: 0 :: 0 :: []).

Eval compute in test.
Eval compute in test2.
Eval compute in test3.

