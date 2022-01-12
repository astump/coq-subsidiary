(* prove that appending the lists returned by Span gives the original list *) 

Require Import Subrec.
Require Import Subreci.
Require Import Mui.
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
  forall (l : list A)(r : List A),
    spanh p xs = SpanSomeMatch l r ->
    S r.

Lemma GuardPresFuni(p : A -> bool) : fmapiT (List A) (GuardPresF p).
  intros X Y f xs gxs l r u.
  apply f.
  exact (gxs l r u).
Qed.

Lemma GuardPresh(p : A -> bool)(S : Mui.kMo (List A)) : Algi (ListF A) ListFi S (GuardPresF p) .
  apply rollAlgi.
  intros R _ _ ih xs fxs .
  destruct fxs.
  + intros l r u ; inversion u.
  + intros l r.
    simpl'.
    change (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p (Subrec.Subrec (ListF A))) t) with (spanh p t).
    destruct (p h) eqn:e.
    ++ destruct (spanh p t) eqn:e2;    
         intro u;
         injection u as u1 u2; rewrite <- u2.
       +++ assumption.
       +++ apply (ih t H l0 l1 e2).
    ++ intro u; discriminate.
Qed.

Definition guardPresh{R : List A -> Prop}(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
                    (p : A -> bool)(xs : List A)(rxs : R xs) : GuardPresF p R xs
 := foi xs (GuardPresF p) (GuardPresFuni p) (GuardPresh p R) rxs.

Lemma guardPres{R : List A -> Prop}(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
      (p : A -> bool)(xs : List A)(rxs : R xs)(l:list A)(r : List A)(e: span p xs = (l,r)) : R r.
 unfold span,spanr in e.
 destruct (spanhr (fold (ListF A)) p xs) eqn:e'; inversion e; rewrite <- H1.
 + assumption. 
 + exact (guardPresh foi p xs rxs l0 s e').
Qed.

End GuardPres.

Arguments guardPres {A} {R} foi p xs rxs {l}{r}.