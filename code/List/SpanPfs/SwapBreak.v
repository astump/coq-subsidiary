(* prove some lemmas about how swap and break interact *) 

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.
Require Import List.Span.
Require Import List.Swap.
Require Import List.ExtraLib.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section swapBreak.

  Variables n m : nat.
  Variable dnm : n <> m.

  Definition neqb(a b : nat) := negb (Nat.eqb a b).

  Definition swapL(l : List nat) : List nat := toList (swap n m (fromList l)).

Definition swapSpanhF(l : List nat) : Prop :=
  (forall (p : list nat)(s : List nat),
     spanh (neqb n) l = SpanSomeMatch p s ->
     spanh (neqb m) (swapL l) = SpanSomeMatch (swap n m p) (swapL s)) /\
  (spanh (neqb n) l = SpanNoMatch ->
  spanh (neqb m) (swapL l) = SpanNoMatch).

Ltac foldSpanh :=
  match goal with
  | |- context[fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat ?p) ?t] =>
    change (fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat p) t) with (spanh p t)
  end.

Lemma SwapSpanhAlg : Algi (ListF nat) ListFi (Consti swapSpanhF).
  apply rollAlgi.
  intros R _ ih xs fxs .
  destruct fxs. 
  - apply conj; [ intros p s u; discriminate u | trivial]. 
  - set (i := ih t H).                                   
    destruct i as [i1 i2].
    apply conj.
    -- intros p s. 
       change (swapL (mkCons h t)) with (mkCons (swap_elt n m h) (swapL t)).
       unfold span, spanr, spanhr; simpl'.
       destruct (neqb n h) eqn:nh.
       --- foldSpanh. 
           destruct (spanh (neqb n) t) eqn:sn; destruct (neqb m (swap_elt n m h)) eqn:v; intro u;
             unfold neqb in nh,v; unfold swap_elt in v.
           ---- inversion u; clear u.
                foldSpanh.
                rewrite H2 in i1, i2.
                rewrite (i2 eq_refl).
                reflexivity.
           ---- split_if.
           ---- foldSpanh.
                rewrite (i1 l l0); trivial.
                injection u; intros u1 u2; clear u.
                rewrite <- u2. 
                rewrite u1.
                reflexivity.
           ---- split_if.
           --- intro u; discriminate u.
        -- unfold spanh, spanhr; simpl'.
           destruct (neqb n h) eqn:nh; foldSpanh.
           --- destruct (spanh (neqb n) t) eqn:sn; intro u; discriminate u.
           --- destruct (neqb m (swap_elt n m h)) eqn:sw; unfold neqb in sw, nh; unfold swap_elt in sw; split_if.
Qed.

Lemma swapSpanhFuni : Mui.fmapiT (List nat) (Consti swapSpanhF).
  intros X Y f xs gxs. exact gxs.
Qed.
  
Definition swapSpanh{R : List nat -> Prop}(foi:forall d : List nat, FoldTi (ListF nat) (Algi (ListF nat) ListFi) R d)
                    (xs : List nat)(rxs : R xs) : swapSpanhF xs
 := foi xs (Consti swapSpanhF) swapSpanhFuni SwapSpanhAlg rxs.

Definition swapSpan{R : List nat -> Prop}(foi:forall d : List nat, FoldTi (ListF nat) (Algi (ListF nat) ListFi) R d)
           (xs : List nat)(rxs : R xs) :
  forall (p p' : list nat)(s s' : List nat),
    break (Nat.eqb n) xs = (p , s) ->
    break (Nat.eqb m) (swapL xs) = (p' , s') ->
    swap n m p = p' /\
    swap n m (fromList s) = fromList s'.
  intros p p' s s'.
  unfold break, breakr, spanr, spanhr.
  repeat foldSpanh.
  destruct (swapSpanh foi xs rxs) as [i1 i2].
  fold (neqb n); fold (neqb m).
  destruct (spanh (neqb n) xs) eqn:sn; intro u.
  - rewrite i2; trivial.
    intro v.  
    injection u; injection v; clear u v.
    intros.
    rewrite <- H0; rewrite <- H2.
    apply conj.
    -- reflexivity.
    -- rewrite <- H1.
       unfold swapL in H.
       rewrite <- H.
       rewrite inj.
       trivial.
    - rewrite (i1 l l0 eq_refl).
      intro v.
      injection u; injection v; clear u v.
      intros.
      rewrite <- H; rewrite <- H1.
      unfold swapL.
      rewrite inj.
      apply conj; trivial.
      congruence.
Qed.

End swapBreak.
