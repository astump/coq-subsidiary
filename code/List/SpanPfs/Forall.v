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
  forall (l : list A)(r : List A),
    span p xs = SpanSomeMatch l r ->
    Forallb p l.

Lemma SpanForall(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) ListFi C (Consti (spanForallF p)) .
  apply rollAlgi.
  intros R _ _ _ ih xs fxs .
  destruct fxs.
  + intros l r u ; inversion u.
  + intros l r.
    simpl'.
    fold (span p t).
    destruct (p h) eqn:e.
    ++ destruct (span p t) eqn:e2;
         intro u;
         injection u as u1 u2;
         rewrite <- u1;
         apply Forall_cons; try assumption.
       +++ apply Forall_nil.
       +++ apply (ih t H l0 l1 e2).
    ++ intro u; discriminate u.
Qed.

Definition spanForall(R : List A -> Prop)(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForallF p xs :=
  foi xs (Consti (spanForallF p)) (FunConsti (spanForallF p)) (SpanForall p R) rxs.

Definition spanForall2F(p : A -> bool)(xs : List A) : Prop :=
  Forallb p (fromList xs) ->
  span p xs = SpanSomeMatch (fromList xs) (nilInit A)
  \/ span p xs = SpanNoMatch true.

Lemma SpanForall2(p : A -> bool)(C : Mui.kMo (List A)) : Algi (ListF A) ListFi C (Consti (spanForall2F p)) .
  apply rollAlgi.
  intros R _ fo _ ih xs fxs .
  destruct fxs as [|h t rt].
  + intro u; apply or_intror; trivial.
  + intro u; apply or_introl.
    change (fromList (consInit A h t)) with (h :: fromList t) in *.
    inversion u as [|h' t' ph' u'].
    simpl'.
    rewrite ph'.
    fold (span p t).
    destruct (ih t rt u') as [ih1| ih1]; rewrite ih1.
    ++ trivial.
    ++ 
destruct (span p t) eqn:e1.
       +++ simpl in ih1; discriminate ih1.
       +++ unfold fm in *; simpl in ih1|-*.
           inversion ih1 as [(ih1a,ih1b)].
           trivial.           
    ++ rewrite (spanNil A R fo p t H ih2).
       unfold fm.
       rewrite <- ih2.
       simpl.
       trivial.
Qed.

Definition spanForall2(R : List A -> Prop)(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForall2F p xs :=
  foi xs (Consti (spanForall2F p)) (FunConsti (spanForall2F p)) (SpanForall2 p R) rxs.

End spanForall.
