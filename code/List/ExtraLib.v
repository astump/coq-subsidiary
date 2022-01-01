Require Import Plus.
Require Import Le.
Require Import Compare_dec.
Require Import PeanoNat.
Require Import Coq.Init.Nat.
Require Import Coq.Lists.List.

Fixpoint lt_false_lte(a b : nat) : a <? b = false -> b <=? a = true.
  intro u.
  destruct a , b ; try reflexivity.
  inversion u.
  change (S a <? S b) with (a <? b) in u.
  change (S b <=? S a) with (b <=? a).
  exact (lt_false_lte a b u).
Qed.

Definition Forallb{A : Set}(p:A -> bool)(xs : list A) : Prop := Forall (fun a => p a = true) xs.

Lemma Foralleqb{A : Set}(eqb:A -> A -> bool)(eq:forall(a a' : A), eqb a a' = true -> a = a')
      (a : A)(xs : list A) : Forallb (eqb a) xs -> xs = repeat a (length xs) .
  induction xs; simpl.
  - trivial.
  - intro u.
    inversion u.
    rewrite (eq a a0 H1) in *.
    rewrite <- (IHxs H2).
    reflexivity.
Qed.

Lemma hopRepeat : forall{A : Set} (n : nat)(a : A)(xs : list A),
    a :: repeat a n ++ xs = repeat a n ++ a :: xs.
  intros. induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Definition liftRel{A:Set}(r:A -> A -> bool)(x y : A) : Prop := r x y = true.