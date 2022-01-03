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

Definition AppendF(p : A -> bool)(xs : List A) : Prop :=
  forall (l : list A)(r : List A),
    span p xs = SpanSomeMatch l r ->
    fromList xs = l ++ (fromList r).

Lemma Append(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) ListFi C (Consti (AppendF p)) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intros l r u; inversion u.
  + intros l r.
    change (fromList (consInit A h t)) with (h :: fromList t).
    simpl'.
    fold (span p t).
    destruct (p h) eqn:e.
    ++ destruct (span p t) eqn:e2;
         intro u;
         injection u as u1 u2;
         rewrite <- u2 , <- u1.
       +++ trivial.
       +++ rewrite (ih t H l0 l1 e2).
           trivial.                        
    ++ intro u. discriminate u.
Qed.

Definition append(R : List A -> Prop)(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : AppendF p xs :=
  foi xs (Consti (AppendF p)) (FunConsti (AppendF p)) (Append p R) rxs.

End Append.

Arguments append{A}{R} foi p xs rxs {l}{r} e.