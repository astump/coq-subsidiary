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

Definition AppendF(p : A -> bool)(_ : List A -> Prop)(xs : List A) : Prop :=
  forall (l : list A)(r : ListF A (List A)),
    span A p xs = (l,r) ->
    fromList xs = l ++ (fromList (inList r)).

Lemma Append(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) (ListFi A) C (AppendF p) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intros l r u .
    injection u as u1 u2.
    rewrite <- u2 , <- u1.
    reflexivity.
  + intros l r.
    change (fromList (consInit A h t)) with (h :: fromList t).
    set (r' := fromList (inList r)).
    destruct (p h) eqn:e.
    ++ simpl'.
       rewrite e.
       destruct (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p (List A)) t)eqn:e2.
       intro u; injection u as u1 u2.
       rewrite (ih t H l0 l1 e2).
       rewrite <- u1.
       set (r'' := fromList (inList l1)).
       simpl.
       unfold r', r''.
       rewrite <- u2.
       destruct l1; reflexivity.
    ++ simpl'.
       rewrite e.
       intro u.
       injection u as u1 u2.
       rewrite <- u1.
       unfold r'.
       rewrite <- u2.
       reflexivity.
Qed.

End Append.
