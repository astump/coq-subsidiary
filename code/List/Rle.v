Require Import Subrec.
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

(*
(*Require Import SpanPfs.Repeat.
*)
*)
Import ListNotations.


Section RLE.

  Context { A : Set}.
  Variable eqb : A -> A -> bool.

  Definition compressSpan : mappedT A (nat * A) :=
    fun R fo hd tl => 
      let (p,s) := spanr fo (eqb hd) tl in
         ((succ (length p),hd), s).

  Definition RleCarr := Const (List (nat * A)).
  Definition RleAlg(C : Set) : Alg (ListF A) C RleCarr :=
    MapThroughAlg compressSpan C.

  Definition rle(xs : List A) : List (nat * A)
    := @fold (ListF A) RleCarr (FunConst (List (nat * A))) (RleAlg (List A)) xs.

  Definition rlel(xs : List A) : list (nat * A)
    := fromList (rle xs).

End RLE.

(* testcases *)

Definition test := rlel eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


