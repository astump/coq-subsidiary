Require Import Program List Psatz.
Local Open Scope list_scope.

Section Span.

  Variable A : Type.

  Section Span.
    Variable p : A -> bool.

    Fixpoint span (l:list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | x::xs => if p x then let (ys, zs) := span xs in (x::ys, zs) else (nil, l)
      end.

    Lemma span_snd_smaller (l:list A) :
      Datatypes.length (snd (span l)) <= Datatypes.length l.
    Proof.
      induction l as [ |a l IHl]; auto.
      simpl. case (p a); auto.
      destruct (span l) as [ys zs]. simpl in *. lia.
    Qed.
  End Span.

  Variable p : A -> bool.

  Definition break := span (fun a => negb (p a)).

  Program Fixpoint wordsBy (l:list A) {measure (Datatypes.length l)} : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsBy tl
        else
          (hd::(fst (break tl)))::(wordsBy (snd (break tl)))
    end.
  Next Obligation.
    simpl. now apply Lt.le_lt_n_Sm, span_snd_smaller.
  Qed.

End Span.

Arguments wordsBy {A} p l.

Fixpoint swap (n m : nat) (l : list nat) : list nat :=
  match l with
  | a :: l' => (if Nat.eqb n a then m
                else if Nat.eqb m a then n
                     else a) :: (swap n m l')
  | _ => nil
  end.

Lemma swap_id : forall (n : nat) (l : list nat),
    swap n n l = l.
Proof.
  induction l; simpl; eauto.
  destruct (Nat.eqb n a) eqn: ?; try congruence.
  apply EqNat.beq_nat_true in Heqb; subst; congruence.
Qed.

Lemma swap_break :
  forall n m l,
    Nat.eqb n m = false ->
    fst (break nat (Nat.eqb n) l) = swap m n (fst (break nat (Nat.eqb m) (swap n m l))).
Proof.
  induction l; simpl; eauto; intros.
  destruct (Nat.eqb n a) eqn: ?; simpl.
  - rewrite PeanoNat.Nat.eqb_refl; simpl; reflexivity.
  - destruct (Nat.eqb m a) eqn: ?; simpl.
     rewrite PeanoNat.Nat.eqb_sym, H; simpl.
     destruct (break nat (Nat.eqb n) l); simpl in *.
     rewrite IHl; eauto.
     destruct (break nat (Nat.eqb m) (swap n m l)); simpl.
     rewrite PeanoNat.Nat.eqb_sym, H; simpl.
     rewrite PeanoNat.Nat.eqb_refl; simpl.
     eapply EqNat.beq_nat_true in Heqb0; subst; eauto.
     rewrite Heqb0; simpl.
     destruct (break nat (Nat.eqb n) l); simpl.
     simpl in *; rewrite IHl; eauto.
     destruct (break nat (Nat.eqb m) (swap n m l)); simpl.
     rewrite Heqb0, Heqb; eauto.
Qed.

Lemma swap_break_snd :
  forall m n l,
    n <> m ->
    swap n m (snd (break nat (Nat.eqb n) l)) = snd (break nat (Nat.eqb m) (swap n m l)).
Proof.
  induction l; simpl.
  - reflexivity.
  - destruct (Nat.eqb n a) eqn: ?; simpl; intros.
    + rewrite Heqb, PeanoNat.Nat.eqb_refl; simpl.
      reflexivity.
    + destruct (Nat.eqb m a) eqn: ?; simpl.
      * destruct (Nat.eqb m n) eqn: ?; simpl.
        -- eapply EqNat.beq_nat_true in Heqb1; congruence.
        -- destruct (break nat (Nat.eqb n) l); simpl in *.
           rewrite IHl by eauto.
           destruct (break nat (Nat.eqb m) (swap n m l)); reflexivity.
      * rewrite Heqb0; simpl.
        destruct (break nat (Nat.eqb n) l); simpl in *.
        rewrite IHl by eauto.
        destruct (break nat (Nat.eqb m) (swap n m l)); reflexivity.
Qed.

Lemma wordsBy_swap : forall n m l,
    wordsBy (Nat.eqb n) l = map (swap m n) (wordsBy (Nat.eqb m) (swap n m l)).
Proof.
  intros.
  assert (forall bnd l, length l <= bnd ->
                     wordsBy (Nat.eqb n) l = map (swap m n) (wordsBy (Nat.eqb m) (swap n m l))).
  clear; induction bnd.
  - destruct l; intros; try reflexivity.
    simpl in H; lia.
  - destruct l; intros; try reflexivity.
    unfold wordsBy; simpl.
    rewrite WfExtensionality.fix_sub_eq_ext; simpl.
    destruct (Nat.eqb n n0) eqn: ?.
    + fold (wordsBy (Nat.eqb n) l).
      rewrite WfExtensionality.fix_sub_eq_ext; simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      rewrite IHbnd; try reflexivity.
      simpl in H; lia.
    + destruct (Nat.eqb m n0) eqn: ?.
      * symmetry.
        rewrite WfExtensionality.fix_sub_eq_ext; simpl.
        symmetry.
        destruct (Nat.eqb m n) eqn: ?.
        -- eapply EqNat.beq_nat_false in Heqb.
           eapply EqNat.beq_nat_true in Heqb0.
           eapply EqNat.beq_nat_true in Heqb1.
           congruence.
        -- simpl; rewrite Heqb1, PeanoNat.Nat.eqb_refl.
           simpl; eapply EqNat.beq_nat_true in Heqb0; subst.
           repeat f_equal.
           ++ eapply swap_break; eauto.
           ++ simpl in *.
              fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
              fold (wordsBy (Nat.eqb n0) (snd (break nat (Nat.eqb n0) (swap n n0 l)))).
              rewrite IHbnd by (etransitivity; [eapply span_snd_smaller | lia]).
              eapply EqNat.beq_nat_false in Heqb.
              rewrite swap_break_snd; eauto.
      * symmetry; rewrite WfExtensionality.fix_sub_eq_ext; simpl; symmetry.
        rewrite Heqb0; simpl.
        rewrite Heqb0; simpl.
        rewrite Heqb; simpl.
        repeat f_equal.
        -- destruct (Nat.eqb n m) eqn: ?.
           ++ eapply EqNat.beq_nat_true in Heqb1; subst.
              rewrite !swap_id; reflexivity.
           ++ eapply swap_break; eauto.
        -- simpl in *.
             fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
             rewrite IHbnd by (etransitivity; [eapply span_snd_smaller | lia]).
             unfold wordsBy; repeat f_equal.
             destruct (Nat.eqb n m) eqn: ?.
           ++ eapply EqNat.beq_nat_true in Heqb1; subst.
              rewrite !swap_id; reflexivity.
           ++ rewrite swap_break_snd; eauto using EqNat.beq_nat_false.
  - eapply H; eauto.
Qed.

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).
