Require Import Lists.List EqNat.
Local Open Scope list_scope.

Definition swap_elt (n m a : nat) : nat :=
  if Nat.eqb n a then m
  else if Nat.eqb m a then n
  else a.

Definition swap(n m : nat) := map (swap_elt n m).

Ltac split_if :=
  repeat
    match goal with
    | |- context[Nat.eqb ?n ?n] =>
        rewrite (PeanoNat.Nat.eqb_refl n); simpl
    | |- context[Nat.eqb ?m ?n] =>
        let Heqb := fresh in
        destruct (Nat.eqb m n) eqn: Heqb; simpl;
        [ apply EqNat.beq_nat_true in Heqb;
          subst; simpl;
          try congruence
        | apply EqNat.beq_nat_false in Heqb;
          try congruence ]
    | H : context[Nat.eqb ?m ?n] |- _ =>
        let Heqb := fresh in
        destruct (Nat.eqb m n) eqn: Heqb; simpl;
        [ apply EqNat.beq_nat_true in Heqb;
          subst; simpl;
          try congruence
        | apply EqNat.beq_nat_false in Heqb;
          try congruence ]
  end.

Lemma swap_elt_id(n a : nat) : swap_elt n n a = a.
  unfold swap_elt.
  split_if.
Qed.

Lemma swap_id : forall (n : nat) (l : list nat),
    swap n n l = l.
Proof.
  induction l; simpl; eauto; unfold swap_elt; split_if.
Qed.
