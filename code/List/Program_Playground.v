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

Lemma swap_id : forall (n : nat) (l : list nat),
    swap n n l = l.
Proof.
  induction l; simpl; eauto; split_if.
Qed.

Lemma swap_break :
  forall n m l,
    n <> m ->
    fst (break nat (Nat.eqb n) l) = swap m n (fst (break nat (Nat.eqb m) (swap n m l))).
Proof.
  induction l; simpl; eauto; intros.
  split_if; eauto.
  -  destruct (break nat (Nat.eqb n) l); simpl in *.
     rewrite IHl; eauto.
     destruct (break nat (Nat.eqb a) (swap n a l)); simpl; split_if.
  - destruct (break nat (Nat.eqb n) l); simpl.
    simpl in *; rewrite IHl; eauto.
    destruct (break nat (Nat.eqb m) (swap n m l)); simpl; split_if.
Qed.

Lemma swap_break_snd :
  forall m n l,
    n <> m ->
    swap n m (snd (break nat (Nat.eqb n) l)) = snd (break nat (Nat.eqb m) (swap n m l)).
Proof.
  induction l; simpl.
  - reflexivity.
  - intros; split_if; eauto.
    + destruct (break nat (Nat.eqb n) l); simpl in *.
      rewrite IHl by eauto.
      destruct (break nat (Nat.eqb a) (swap n a l)); reflexivity.
    + destruct (break nat (Nat.eqb n) l); simpl in *.
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
    (* Is there a better way to simplify wordsBy than unfolding / rewriting / folding? *)
    unfold wordsBy at 1; simpl.
    rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
    + fold (wordsBy (Nat.eqb n0) l).
      (* We also have to do this to simplify the occurence of wordsBy on the righthand side: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      simpl in *; rewrite IHbnd by lia; try reflexivity.
    + fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
      (* We again have to do this to simplify the occurence of wordsBy on the righthand side: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl.
      fold (wordsBy (Nat.eqb n0) (snd (break nat (Nat.eqb n0) (swap n n0 l)))).
      split_if.
      repeat f_equal.
      * eapply swap_break; eauto.
      * rewrite IHbnd by (etransitivity; [eapply span_snd_smaller | simpl in *; lia]).
        rewrite swap_break_snd by eauto; reflexivity.
    + fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
      (* And one last time: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      fold (wordsBy (Nat.eqb m) (snd (break nat (Nat.eqb m) (swap n m l)))).
      rewrite IHbnd by (etransitivity; [eapply span_snd_smaller | simpl in *; lia]).
      destruct (Nat.eqb n m) eqn: Heqb ;
        [eapply EqNat.beq_nat_true in Heqb; subst
        | eapply EqNat.beq_nat_false in Heqb].
      * rewrite !swap_id; eauto.
      * erewrite swap_break, swap_break_snd; eauto.
  - eapply H; eauto.
Qed.

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).
