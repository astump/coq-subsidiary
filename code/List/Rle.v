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
(*Require Import SpanPfs.Repeat.
*)
Import ListNotations.


Section RLE.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
  Variable eqRefl : forall a , eqb a a = true.

  Definition RleCarr := Const (list (nat * A)).
  Definition RleAlg : Alg (ListF A) (List A) RleCarr :=
    rollAlg (fun R reveal fo out eval xs =>
          match xs with
          | Nil => []
          | Cons hd tl =>
            match spanr fo (eqb hd) tl with
              SpanNoMatch => (1,hd) :: eval tl
            | SpanSomeMatch p s => (succ (length p),hd) :: eval s
            end
          end).

  Definition rle(xs : List A) : list (nat * A)
    := @fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg xs.

  Theorem RldRle : forall (xs : list A), rld (rle (toList xs)) = xs.
    intros xs.
    listInd (fun (X : List A -> Prop) xs => rld (rle xs) = fromList xs) xs; trivial.
    - change (fromList (consInit A h t)) with (h :: fromList t). 
      simpl'.
      fold (rle t).
      destruct (spanr (fold (ListF A)) (eqb h) t) as [|l r] eqn:e.
      -- simpl.
         rewrite (ih t H).
         trivial.
      -- fold (rle r).
         simpl.
         rewrite (ih r (guardPres fo (eqb h) t H e)).
         rewrite (append fo (eqb h) t H e).
      set (sf := spanForall A R fo (eqb h) t H l r e).
      rewrite <- (Foralleqb eqb eq h l sf).
      trivial.
    - exact (toListi _ xs).
    Qed.

Theorem RleRepeat(a : A)(n : nat) :
    rle (toList (repeat a (S n))) = [(S n,a)].
  
  simpl'.  
  fold (toList (repeat a n)).
  Check spanForall2.
  Check foldi.
  set (sf := spanForall2 A (Listi A) foldi (eqb a) (toList (repeat a n)) (toListi A (repeat a n))).
  unfold spanForall2F in sf.
  rewrite (inj (repeat a n)) in sf.
  destruct (sf (Foralleqb2 eqb eqRefl a n)) as [ih1|ih2].
  destruct (span (eqb a) (toList (repeat a n))) eqn:e.
  + simpl in ih1; discriminate ih1.
  + simpl in ih1.       
    unfold span in e.
    unfold spanr.
    change (Subrec.Subrec (ListF A)) with (List A).
    rewrite e.
    inversion ih1 as [(ih1a,ih1b)].
    fold (rle l0).
    admit.
  + rewrite ih2.
    simpl'.
    destruct n.
    ++ trivial.
    ++ simpl in ih2; discriminate ih2.
Qed.

End RLE.

(* testcases *)

Definition test := rle nat eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


