(* prove that appending the lists returned by Span gives the original list *) 

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import List.Span.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section Append.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition SpanAppendF(p : A -> bool)(xs : List A) : Prop :=
    let (l,r) := span p xs in
      fromList xs = l ++ (fromList r).

Lemma SpanAppend(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) ListFi C (Consti (SpanAppendF p)) .
  apply rollAlgi.
  intros R _ _ ih xs fxs .
  destruct fxs.
  + reflexivity.
  + hnf.
    change (fromList (mkCons h t)) with (h :: fromList t).
    unfold span,spanr,spanhr; simpl'.
    change (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p (Subrec.Subrec (ListF A))) t) with (spanh p t).
    destruct (p h) eqn:e; destruct (spanh p t) eqn:e'; trivial.
    ++ set (ih1 := ih t H).
       unfold Consti, SpanAppendF,span,spanr in ih1.
       unfold spanh in e'.       
       rewrite e' in ih1.
       rewrite ih1.      
       reflexivity.
Qed.

Definition spanAppend{R : List A -> Prop}(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : SpanAppendF p xs :=
  foi xs (Consti (SpanAppendF p)) (FunConsti (SpanAppendF p)) (SpanAppend p R) rxs.

End Append.

Arguments spanAppend{A}{R}.