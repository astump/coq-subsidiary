Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import Mu.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Require Import List.List.

Import ListNotations.

Section ListPfs.

Context {A : Set}.

Definition getNilIdemP(xs : List A) : Prop := getNil (getNil xs) = getNil xs.

Definition getNilIdem{R : List A -> Prop}
           (foi:forall d : List A, FoldTi (ListF A) (Algi (ListF A) ListFi) R d)
           (xs : List A)(rxs : R xs) : getNilIdemP xs.
  apply (foi xs (Consti getNilIdemP) (FunConsti getNilIdemP)).
  apply rollAlgi.  
  + intros S _ _ ih d fd.
    destruct fd.
    ++ reflexivity.
    ++ unfold Consti, getNilIdemP,getNil. simpl'.
       change (fold (ListF A) option FunOption (getNilAlg A (List A)) t) with (getNilh t).
       destruct (getNilh t) eqn:e.
       +++ set (ih1 := ih t H).
           unfold Consti,getNilIdemP,getNil in ih1.
           rewrite e in ih1. 
           exact ih1.
       +++ rewrite e.
           trivial.
  + exact rxs.
Qed.

End ListPfs.