(* similar to wordsBy from Haskell's Data.List.Extra *)

Require Import Subrec.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import ExtraLib.
Require Import Span.
Require Import SpanPfs.Forall.
Require Import SpanPfs.GuardPres.

Import ListNotations.

Section WordsBy.

  Variable A : Set.
  
  Definition WordsByAlg(p : A -> bool)
    : Alg (ListF A) (Const (list (list A))) :=
    rollAlg 
      (fun R fo wordsBy xs => 
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
    fo (Const (list (list A))) (FunConst (list (list A))) (WordsByAlg p) xs.

  Definition wordsBy(p : A -> bool)(xs : List A) : list (list A) :=
    wordsByr (fold (ListF A)) p xs.

  Definition wordsByl(p : A -> bool)(xs : list A) : list (list A) :=
    wordsBy p (toList xs).

  Definition wordsByOutputsNegT(p : A -> bool)(xs : List A) : Prop :=
    Forall (Forallb (fun x => negb (p x))) (wordsBy p xs).

  Theorem wordsByOutputsNeg(p : A -> bool)(xs : list A) : wordsByOutputsNegT p (toList xs).  
  listInd (fun (X : List A -> Prop) => wordsByOutputsNegT p) xs.
  + apply Forall_nil.
  + unfold wordsByOutputsNegT.
    simpl'.
    change (fold (ListF A) (Const (list (list A))) (FunConst (list (list A))) (WordsByAlg p) t) with (wordsBy p t).
    destruct (p h) eqn:e.
    ++ exact (ih t H).
    ++ destruct (breakr (fold (ListF A)) p t) eqn:e'.
       apply Forall_cons.
       +++ apply Forall_cons.
           ++++ rewrite e; trivial.
           ++++ apply (spanForall fo (fun x : A => negb (p x))t H e').
       +++ apply ih.
           exact (guardPres fo (fun x : A => negb (p x)) t H e').
Qed.

  Theorem wordsByInputNegT(p : A -> bool)(xs : list A) :
    Forallb p xs ->
    wordsBy p (toList xs) = nil.
    induction xs; intro H.
    - simpl'; trivial.
    - simpl'.
      inversion H.
      destruct (p a) eqn:e.
      -- exact (IHxs H3).
      -- discriminate H2.
   Qed.

End WordsBy.

Arguments wordsByr{A}{R}.
Arguments wordsBy{A}.
Arguments wordsByl{A}.

(* testcases *)

(*
(* 0 will play the role of a space *)
Definition test := wordsBy (eqb 0) (toList (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: [])).

Eval compute in test.

Definition t1 := repeat 0 1000.

Eval compute in (wordsBy (eqb 0) (toList (t1 ++ 1 :: 1 :: 2 :: (t1 ++ 1 :: 3 :: 5 :: 0 :: nil)))).

*)