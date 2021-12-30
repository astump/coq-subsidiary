Require Import Plus.
Require Import Le.
Require Import Compare_dec.
Require Import PeanoNat.

Fixpoint lt_false_lte(a b : nat) : a <? b = false -> b <=? a = true.
  intro u.
  destruct a , b ; try reflexivity.
  inversion u.
  change (S a <? S b) with (a <? b) in u.
  change (S b <=? S a) with (b <=? a).
  exact (lt_false_lte a b u).
Qed.
