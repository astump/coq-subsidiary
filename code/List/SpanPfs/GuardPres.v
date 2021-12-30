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

Section GuardPres.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition GuardPresF(p : A -> bool)(S : List A -> Prop)(xs : List A) : Prop :=
  forall (l : list A)(r : ListF A (List A)),
    span A p xs = (l,r) ->
    ListFi A S (inL r).

Lemma GuardPres(p : A -> bool)(S : Mui.kMo (List A)) : Algi (ListF A) (ListFi A) S (GuardPresF p) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intros l r u .
    injection u as u1 u2.
    rewrite <- u2.
    apply nilFi.
  + intros l r.
    destruct (p h) eqn:e.
    ++ simpl'.
       rewrite e.
       destruct (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p (List A)) t) eqn:e2.
       intro u; injection u as u1 u2.
       destruct l1; rewrite <- u2.
       +++ apply nilFi.
       +++ apply consFi.
           set (q := ih t H l0 (Cons a s) e2).
           inversion q.
           ++++ destruct (nilCons A a s H0).
           ++++ destruct (consCons A h0 a t0 s H1).
                rewrite <- H3.
                assumption.
    ++ simpl'.
       rewrite e.
       intro u; injection u as u1 u2.
       rewrite <- u2.
       apply consFi.
       assumption.
Qed.

End GuardPres.
