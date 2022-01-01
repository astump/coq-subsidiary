(* run-length encoding with a single recursion, for comparison *)

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Mu.
Require Import List.
Require Import Functors.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Require Import List.Repeat.
Require Import Rld.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.


Section RLE.

Variable A : Set.
Variable eqb : A -> A -> bool.
Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
Variable eqRefl : forall a , eqb a a = true.
    
Fixpoint rleh(xs:list A)(e : option (nat * A)):list (nat * A) :=
  match xs with
    nil => match e with
             None => []
           | Some e => [ e ]
           end
  | cons h t =>
    match e with
      None => rleh t (Some (1,h))
    | Some (n,h') =>
      if eqb h h' then
        rleh t (Some (1+n,h'))
      else
        (n,h')::rleh t (Some (1,h))
    end
  end.

Definition rle(xs:list A) : list (nat * A) := rleh xs None.

Definition expand(e : option(nat * A)) : list A :=
  match e with
    None => []
  | Some (n,a) => repeat n a
  end.

Theorem rleRld(xs : list A) :
  forall(e : option (nat * A)),
    rld (rleh xs e) = expand e ++ xs.
  induction xs; intro e.
  + simpl.
    destruct e as [(n,a)|]; reflexivity.
  + destruct e as [(n,a')|].
    ++ simpl.
       destruct (eqb a a') eqn:u.
       +++ rewrite (IHxs (Some (S n,a'))).
           simpl.
           rewrite (hopRepeat n a' xs).
           rewrite (eq a a' u).
           reflexivity.
       +++ simpl.
           rewrite (IHxs (Some (1,a))).
           simpl.
           reflexivity.
    ++ simpl.
       rewrite (IHxs (Some (1,a))).
       simpl.
       reflexivity.
Qed.

Theorem rleRepeat(a : A)(n : nat) :
  rleh (repeat (S n) a) None = [(S n,a)] /\
  forall k : nat , rleh (repeat n a) (Some (k,a)) = [(k+n,a)].
induction n.
+ simpl.
  apply conj.
  ++ reflexivity.
  ++ intro k.
     rewrite (plus_0_r k).
     reflexivity.
+ apply conj.
  ++ simpl.
     rewrite (eqRefl a).
     rewrite (proj2 IHn 2).
     reflexivity.
  ++ intro k.
     simpl.
     rewrite (eqRefl a).
     rewrite (proj2 IHn (S k)).
     rewrite (plus_Snm_nSm k n).
     reflexivity.
Qed.

End RLE.

(* testcases *)

Definition test := rle nat eqb (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: []).

Eval compute in test.


