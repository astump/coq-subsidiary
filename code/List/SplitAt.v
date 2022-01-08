(* similar to wordsBy from Haskell's Data.List.Extra *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import Span.

Import ListNotations.

Section SplitAt.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
  
  Inductive SplitAtF(X : Set) : Set :=
    SplitAtZ : SplitAtF X
  | SplitAtS : list A -> X -> SplitAtF X.

  Definition SplitAtF1(X : Set) : Set := nat -> SplitAtF X.

  Arguments SplitAtZ{X}.
  Arguments SplitAtS{X}.

  Global Instance SplitAtFunctor : Functor SplitAtF1 :=
    {fmap X Y f c := fun n =>
       match c n with
         SplitAtZ => SplitAtZ
       | SplitAtS l x => SplitAtS l (f x)
       end
    }.
  
  Definition SplitAtAlg(C : Set)
    : Alg (ListF A) C SplitAtF1 :=
    rollAlg 
      (fun R reveal fo splitAt xs n => 
         match xs with
           Nil => SplitAtZ 
         | Cons hd tl =>
           match n with
             O => SplitAtZ
           | S n' =>
              match (splitAt tl n') with
                SplitAtZ => SplitAtS [hd] tl
              | SplitAtS l r => SplitAtS (hd::l) r
              end
           end
         end).

  Definition splitAthr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                      (xs : R) : SplitAtF1 R :=
    fo SplitAtF1 SplitAtFunctor (SplitAtAlg R) xs.

  Definition splitAth(xs : List A) : SplitAtF1 (List A) :=
    splitAthr (fold (ListF A)) xs.

  Definition splitAtr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                     (n : nat)(xs : R) : list A * R :=
    match splitAthr fo xs n with
      SplitAtZ => ([],xs)
    | SplitAtS l r => (l,r)
    end.

  Definition splitAt : nat -> List A -> list A * List A
    := splitAtr (fold (ListF A)).

  (* intended just for testing below *)
  Definition splitAtl(n : nat)(xs : list A) : list A * list A :=
    let (l,r) := splitAt n (toList xs) in
      (l,fromList r).

End SplitAt.

Arguments splitAtr{A}{R}.
Arguments splitAt{A}.
Arguments splitAth{A}.
Arguments splitAthr{A}{R}.
Arguments splitAtl{A}.
Arguments SplitAtZ{A}{X}.
Arguments SplitAtS{A}{X}.

(* testcases *)

Definition test := splitAtl 3 (1 :: 1 :: 2 :: 2 :: 1 :: 3 :: 5 :: []).
Definition test2 := splitAtl 3 (1 :: 1 :: []).
Definition test3 := splitAtl 0 (1 :: 1 :: []).

Eval compute in test.
Eval compute in test2.
Eval compute in test3.

