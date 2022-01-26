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
    span p xs = (l,r) ->
    Forallb p l.

Lemma SpanForall(p : A -> bool) : Algi (ListF A) ListFi (Consti (spanForallF p)) .
  apply rollAlgi.
  intros R _ ih xs fxs l r .
  destruct fxs.
  + intro e; inversion e; apply Forall_nil.
  + unfold span, spanr, spanhr. simpl'.
    change (Subrec.Subrec (ListF A)) with (List A).
    change (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p) t) with (spanh p t).
    destruct (p h) eqn:e.
    ++ destruct (spanh p t) eqn:e'; intro u; inversion u as [(u1,u2)]; clear u; apply Forall_cons; try assumption.
       +++ apply Forall_nil.
       +++ set (i := ih t H l0 l1).
           unfold span, spanr in i.
           unfold spanh in e'.
           rewrite e' in i.
           apply i.
           reflexivity.
    ++ intro u; inversion u; apply Forall_nil.
Qed.

Definition spanForall{R : List A -> Prop}(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForallF p xs :=
  foi xs (Consti (spanForallF p)) (FunConsti (spanForallF p)) (SpanForall p) rxs.


Definition spanForall2F(p : A -> bool)(xs : List A) : Prop :=
  Forallb p (fromList xs) ->
  span p xs = (fromList xs, getNil xs).

Lemma SpanForall2(p : A -> bool) : Algi (ListF A) ListFi (Consti (spanForall2F p)) .
  apply rollAlgi.
  intros R fo ih xs fxs .
  destruct fxs as [|h t rt].
  + intro u; trivial.
  + intro u.
    change (fromList (mkCons h t)) with (h :: fromList t) in *.
    inversion u as [|h' t' ph' u'].
    unfold span, spanr,spanhr. simpl'.
    rewrite ph'.
    change (fold (ListF A) (SpanF A) (SpanFunctor A) (SpanAlg A p) t) with (spanh p t).
    set (ih1 := ih t rt u').
    unfold span , spanr in ih1.
    destruct (spanh p t) eqn:e; unfold spanh in e; rewrite e in ih1.
    ++ inversion ih1 as [(ih1a, ih1b)].
       assert (q : getNil t = getNil (mkCons h (getNil t))).
       +++ rewrite <- ih1b.
           unfold getNil; simpl'.
           change (fold (ListF A) (fun A0 : Set => option A0) FunOption (getNilAlg A (List A)) t) with (getNilh t).
           unfold getNil in ih1b.
           destruct (getNilh t) eqn:e'; assumption.
       +++ rewrite <- q.
           trivial.
    ++ injection ih1 as ih1a ih1b.
       rewrite <- ih1a.
       assert (q : l0 = getNil (mkCons h t)).
       +++ unfold getNil; simpl'.
           change (fold (ListF A) (fun A0 : Set => option A0) FunOption (getNilAlg A (List A)) t) with (getNilh t).
           destruct (getNilh t) eqn:e';unfold getNil in ih1b; rewrite e' in ih1b; assumption.
    +++ rewrite <- q; trivial.
Qed.

Definition spanForall2{R : List A -> Prop}(foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (p : A -> bool)(xs : List A)(rxs : R xs) : spanForall2F p xs :=
  foi xs (Consti (spanForall2F p)) (FunConsti (spanForall2F p)) (SpanForall2 p) rxs.

End spanForall.

Arguments spanForall{A}{R} foi p xs rxs {l}{r}.
Arguments spanForall2{A}{R}.