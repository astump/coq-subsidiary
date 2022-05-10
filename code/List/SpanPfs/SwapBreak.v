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

Definition swapBreakF(l : List nat) : Prop :=
  (forall (p : list nat)(s : List nat),
     spanh (neqb n) l = SpanSomeMatch p s ->
     spanh (neqb m) (swapL l) = SpanSomeMatch (swap n m p) (swapL s)) /\
  (spanh (neqb n) l = SpanNoMatch ->
  spanh (neqb m) (swapL l) = SpanNoMatch).

Lemma SwapBreakAlg : Algi (ListF nat) ListFi (Consti swapBreakF).
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
       --- change (fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat (neqb n)) t) with (spanh (neqb n) t).
           destruct (spanh (neqb n) t) eqn:sn; destruct (neqb m (swap_elt n m h)) eqn:v; intro u;
             unfold neqb in nh,v; unfold swap_elt in v.
           ---- inversion u; clear u.
                change (fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat (neqb m)) (swapL s)) with
                       (spanh (neqb m) (swapL s)).
                rewrite H2 in i1, i2.
                rewrite (i2 eq_refl).
                reflexivity.
           ---- split_if.
           ---- change (fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat (neqb m)) (swapL t)) with
                       (spanh (neqb m) (swapL t)).
                rewrite (i1 l l0); trivial.
                injection u; intros u1 u2; clear u.
                rewrite <- u2. 
                rewrite u1.
                reflexivity.
           ---- split_if.
           --- intro u; discriminate u.
        -- unfold spanh, spanhr; simpl'.
           destruct (neqb n h) eqn:nh;
             change (fold (ListF nat) (SpanF nat) (SpanFunctor nat) (SpanAlg nat (neqb n)) t) with
                       (spanh (neqb n) t).
           --- destruct (spanh (neqb n) t) eqn:sn; intro u; discriminate u.
           --- destruct (neqb m (swap_elt n m h)) eqn:sw.

