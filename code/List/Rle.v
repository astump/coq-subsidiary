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

Require Import List.ExtraLib.
Require Import Rld.

Require Import Span.
Require Import SpanPfs.Append.
Require Import SpanPfs.Forall.
Require Import SpanPfs.GuardPres.
Require Import SpanPfs.Repeat.

Import ListNotations.


Section RLE.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
  Variable eqRefl : forall a , eqb a a = true.

    
  (* -------------------------------------------------------------------------------- *)
  (* Run-Length encode *)
  (* -------------------------------------------------------------------------------- *)

  Definition tackOn(prev : A)(xs : list (nat * A)) : list (nat * A) :=
    match xs with
      [] => [(1,prev)]
    | (count,x) :: xs' =>
      if eqb prev x then
        (succ count,x) :: xs'
      else
        (1,prev) :: xs
    end.

  Definition RleCarr := Const (list (nat * A)).
  Definition RleAlg : Alg (ListF A) (List A) RleCarr :=
    rollAlg (ListF A)
            (fun R reveal fo out eval xs =>
          match xs with
          | Nil => []
          | Cons hd tl =>
            let (p,s) := spanr fo (eqb hd) tl in
            let e := (succ (length p), hd) in
                match s with
                  Nil          => [e]
                | Cons hd' tl' => e :: tackOn hd' (eval tl')
                end
          end).

  Definition rle(xs : List A) : list (nat * A)
    := @fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg xs.

  Lemma rldTackOn(a : A)(xs : list (nat * A)) :
                 rld (tackOn a xs) = a :: rld xs.
  case xs as [|h t]; simpl; trivial.
  destruct h as [n a'].
  destruct (eqb a a') eqn:e; trivial.
  rewrite (eq a a' e).
  trivial.
  Qed.

  Theorem RldRle : forall (xs : list A), rld (rle (toList xs)) = xs.
    intros xs.
    listInd (fun (X : List A -> Prop) xs => rld (rle xs) = fromList xs) xs; trivial.
    - change (fromList (consInit A h t)) with (h :: fromList t). 
      simpl'.
      change (fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg) with rle.
      destruct (spanr (fold (ListF A)) (eqb h) t) as (l,r) eqn:e.
      rewrite (append fo (eqb h) t H e).
      set (sf := spanForall A R fo (eqb h) t H l r e).
      set (uu := Foralleqb eqb eq h l sf).
      destruct r as [|h' t'].
      -- simpl'.
         rewrite <- uu.
         trivial.
      -- set (sg := guardPres fo (eqb h) t H e).
         inversion sg as [e'|h'' t'' rt'' e'].
      --- contradiction (nilCons e').
      --- destruct (consCons e') as (_, q).
          rewrite q in rt''; clear q.
          change (fromList (inList (Cons h' t'))) with (h' :: fromList t').
          simpl'.
          rewrite (rldTackOn h' (rle t')).
          rewrite (ih t' rt'').
          rewrite <- uu.
          trivial.
    - exact (toListi _ xs).
    Qed.

Theorem RleRepeat(a : A)(n : nat) :
    rle (toList (repeat a (S n))) = [(S n,a)].
  simpl'.  
  change (listFold (repeat a n) (inn (ListF A))) with (toList (repeat a n)).
  rewrite (Repeat A (eqb a) a (eqRefl a) n).
  rewrite (repeat_length a n).
  trivial.
Qed.

End RLE.

(* testcases *)

Definition test := rle nat eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


