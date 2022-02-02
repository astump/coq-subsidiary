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

Require Import MapThrough.
Require Import Span.
Require Import Rld.
Require Import SpanPfs.Forall.
Require Import SpanPfs.GuardPres.
Require Import SpanPfs.Append.


(*
(*Require Import SpanPfs.Repeat.
*)
*)
Import ListNotations.


Section RLE.

  Context { A : Set}.
  Variable eqb : A -> A -> bool.
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
  Variable eqRefl : forall a , eqb a a = true.

  Definition compressSpan : mappedT A (nat * A) :=
    fun R fo hd tl => 
      let (p,s) := spanr fo (eqb hd) tl in
         ((succ (length p),hd), s).

  Definition RleCarr := Const (list (nat * A)).
  Definition RleAlg : Alg (ListF A) RleCarr :=
    MapThroughAlg compressSpan.

  Definition rle(xs : List A) : list (nat * A)
    := fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg xs.

  Theorem RldRle (xs : list A): rld (rle (toList xs)) = xs.  
  listInd (fun (X : List A -> Prop) xs => rld (rle xs) = fromList xs) xs.
  + trivial.
  + unfold rle, rle; simpl'; unfold compressSpan.
   destruct (span (eqb h) t) as (p,s) eqn:e.
   unfold span in e.
   rewrite e.
   fold (rle s).
   fromCons.
   simpl.
   fold (rle s).
   rewrite (ih s (guardPres fo (eqb h) t H e)).
   rewrite <- (Foralleqb eqb eq h p (spanForall fo (eqb h) t H e)).
   rewrite (spanAppend fo (eqb h) t H e).
   trivial.
Qed.

(*
  Theorem RldRle' (xs : list A): rld (rle (toList xs)) = xs.  
    change (rle (toList xs)) with (fromList (mapThrough compressSpan (toList xs))).
    rewrite <- (mapThroughInd (nat * A) compressSpan (fun xs ys => fromList xs = rld (fromList ys))
               (toList xs)).
    + apply inj.
    + trivial.
    + clear xs.
      intros a (n,a') xs xs' ys R fo rxs.
      unfold compressSpan.
      change (spanr (fold (ListF A)) (eqb a)) with (span (eqb a)).
      destruct (span (eqb a) xs) eqn:e.
      intros u1 u2. 
      fromCons.
      simpl.
      rewrite <- u2.
      rewrite (spanAppend fo (eqb a) xs rxs e).
      inversion u1 as [(u1a, u1b, u1c)]; clear u1; elim u1b.
      simpl.
      rewrite <- (Foralleqb eqb eq a l (spanForall fo (eqb a) xs rxs e)).
      reflexivity.
Qed.
*)      
End RLE.

(* testcases *)

Definition test := rle eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


