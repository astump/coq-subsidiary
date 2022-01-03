(* for t a List,
   if fromList t = [], then span t = SpanNoMatch *)
 
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

Section spanNil.

Variable A : Set.
Variable eqb : A -> A -> bool.

Definition spanNilF(p : A -> bool)(xs : List A) : Prop :=
    fromList xs = [] ->
    span p xs = SpanNoMatch.

Lemma SpanForall(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) ListFi C (Consti (spanNilF p)) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intro u; trivial.
  + intro u.
    discriminate u.
Qed.

Definition spanNil(R : List A -> Prop)(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanNilF p xs :=
  foi xs (Consti (spanNilF p)) (FunConsti (spanNilF p)) (SpanForall p R) rxs.

End spanNil.
