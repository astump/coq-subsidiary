(* run-length encoding with a single recursion, for comparison *)

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Mu.
Require Import List.
Require Import Functors.

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Require Import ExtraLib.
Require Import PairwiseDistinct.
Require Import Rld.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.


Section RLE.

Variable A : Set.
Variable eqb : A -> A -> bool.
Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
Variable eqRefl : forall a , eqb a a = true.
    
Fixpoint rleh(xs:list A)(n : nat)(h' : A):list (nat * A) :=
  match xs with
    nil => [ (n,h') ]
  | cons h t =>
      if eqb h h' then
        rleh t (S n) h'
      else
        (n,h')::rleh t 1 h 
  end.

Definition rle(xs:list A) : list (nat * A) :=
  match xs with
    nil => []
  | cons h t => rleh t 1 h
  end.

Theorem rlehRld(xs : list A) :
  forall(n : nat)(h' : A),
    rld (rleh xs n h') = repeat h' n ++ xs.
  induction xs as [|h t]; intros n h'; trivial.
  simpl.
  destruct (eqb h h') eqn:u.
  + rewrite (IHt (S n) h').
    simpl.
    rewrite (hopRepeat n h' t).
    rewrite (eq h h' u).
    trivial.
  + simpl.
    rewrite (IHt 1 h).
    trivial.
Qed.

Theorem rleRld(xs : list A) :
  rld (rle xs) = xs.
  case xs; trivial.
  intros a l.
  apply rlehRld.  
Qed.

Theorem rlehRepeat(a : A)(n : nat) :
  forall k : nat , rleh (repeat a n) k a = [(k+n,a)].
induction n; intro k; simpl.
+ rewrite (plus_0_r k).
  reflexivity.
+ rewrite (eqRefl a).
  rewrite (IHn (S k)).
  rewrite (plus_Snm_nSm k n).
  trivial.
Qed.

Theorem rleRepeat(a : A)(n : nat) :
  rle (repeat a (S n)) = [(S n,a)].
  apply rlehRepeat.
Qed.

(*
Theorem rleDistinct(xs : list A):
  forall(n:nat)(h':A),
    PairwiseDistinct eqb (map (@snd nat A) (rleh xs n h')).
  induction xs as [|h t]; intros n h'; simpl.
  + apply LSorted_cons1.
  + destruct (eqb h h') eqn:e.
    ++ apply IHt.
    ++ simpl. 
       apply LSorted_consn.
*)
End RLE.

(* testcases *)

Definition test := rle nat eqb (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: []).

Eval compute in test.


