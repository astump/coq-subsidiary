(* prove that all elements in the first list returned by span satisfy the predicate *) 

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import List.Span.
Require Import List.ExtraLib.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section spanForall.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition spanForallF(p : A -> bool)(xs : List A) : Prop :=
  forall (l : list A)(r : ListF A (List A)),
    span A p xs = (l,r) ->
    Forallb p l.

Lemma SpanForall(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) (ListFi A) C (Consti (spanForallF p)) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intros l r u .
    injection u as u1 u2.
    rewrite <- u1.
    apply Forall_nil.
  + intros l r.
    destruct (p h) eqn:e.
    ++ simpl'.
       rewrite e.
       destruct (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p (List A)) t) as (l',r') eqn:e2.
       intro u; injection u as u1 u2.
       rewrite <- u1.
       apply Forall_cons.
       +++ assumption.
       +++ exact (ih t H l' r' e2).
    ++ simpl'.
       rewrite e.
       intro u; injection u as u1 _.
       rewrite <- u1.
       apply Forall_nil.
Qed.

Definition spanForall(R : List A -> Prop)(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) (ListFi A)) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForallF p xs :=
  foi xs (Consti (spanForallF p)) (FunConsti (spanForallF p)) (SpanForall p R) rxs.

End spanForall.
