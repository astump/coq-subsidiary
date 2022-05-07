Require Import Program List Psatz.
Require Import Lists.List.
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

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

(* Here is a simple example of how using Program complicates reduction
   in *proofs* as well.  We'll prove that (more or less) if we
   consistently update the element used to split a list, it won't
   effect the behavior of [wordsBy]: *)

(* Lemma wordsBy_swap : forall n m l,
    wordsBy (Nat.eqb n) l = map (swap m n) (wordsBy (Nat.eqb m) (swap n m l)).
    Proof.  *)

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
  (* Note that we cannot do induction directly over l, and thus need
     to prove a stronger statement. We have two (morally equivalent)
     choices: *)
  (* - strong induction over the length of the input list OR
     - use the well_founded_induction. *)
  (* We will pursure the first approach here, then use the second
     approach in the following [wordsBy_swap'] lemma. *)

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
      (* Note that in order to use the induction hypothesis, we have
         to prove that the recursive application is to a 'smaller'
         term. *)
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

(* Here's the promised alternative proof using well founded
   induction.*)

Lemma wordsBy_swap' : forall n m l,
    wordsBy (Nat.eqb n) l = map (swap m n) (wordsBy (Nat.eqb m) (swap n m l)).
Proof.
  intros.
  pattern l.
  eapply well_founded_induction with (R := fun l l' => length l < length l').
  - (* We need an auxiliary lemma that less than on measures
       (functions from a type to [nat], is well_founded. Such a proof would
       would need to be manually supplied for more exotic relations. *)
    eapply Wf_nat.well_founded_ltof.
  - intros.
    clear l; destruct x as [ | n0 l ]; intros; try reflexivity.
    (* Is there a better way to simplify wordsBy than unfolding / rewriting / folding? *)
    unfold wordsBy at 1; simpl.
    rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
    + fold (wordsBy (Nat.eqb n0) l).
      (* We also have to do this to simplify the occurence of wordsBy on the righthand side: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      simpl in *; rewrite H by lia; try reflexivity.
    + fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
      (* We again have to do this to simplify the occurence of wordsBy on the righthand side: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl.
      fold (wordsBy (Nat.eqb n0) (snd (break nat (Nat.eqb n0) (swap n n0 l)))).
      split_if.
      repeat f_equal.
      * eapply swap_break; eauto.
      * (* Again, we cannot get away from needing to prove that the
         recursive application is to a 'smaller' term. *)
        rewrite H, swap_break_snd; eauto.
        generalize (span_snd_smaller _ (fun a : nat => negb (Nat.eqb n a)) l);
          unfold break; simpl; intros; lia.
    + fold (wordsBy (Nat.eqb n) (snd (break nat (Nat.eqb n) l))).
      (* And one last time: *)
      unfold wordsBy at 2;
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      fold (wordsBy (Nat.eqb m) (snd (break nat (Nat.eqb m) (swap n m l)))).
      rewrite H.
      * destruct (Nat.eqb n m) eqn: Heqb ;
          [eapply EqNat.beq_nat_true in Heqb; subst
          | eapply EqNat.beq_nat_false in Heqb].
        -- rewrite !swap_id; eauto.
        -- erewrite swap_break, swap_break_snd; eauto.
      * generalize (span_snd_smaller _ (fun a : nat => negb (Nat.eqb n a)) l);
          unfold break; simpl; intros; lia.
Qed.

From Coq Require Vector.

Section DefEqPlayground.

  Program Fixpoint add' (n m : nat) {measure n} : nat :=
    match n with
    | S n' => S (add' n' m)
    | 0 => m
    end.

  Lemma add'_commute : forall (n m : nat), add' n m = add' m n.
  Proof.
    induction n; simpl; intros.
    - unfold add' at 1; simpl.
      unfold add'_func.
      rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      induction m; simpl.
      + reflexivity.
      + unfold add' at 1; simpl.
        unfold add'_func.
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
        rewrite IHm at 1.
        reflexivity.
    - unfold add' at 1; simpl.
      unfold add'_func.
      rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
      fold (add' m n).
      match goal with
        |- S ?x = _ => replace x with (add' n m) by reflexivity
      end.
      rewrite IHn.
      induction m; simpl.
      + reflexivity.
      + unfold add'; simpl.
        unfold add'_func.
        rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
        symmetry; rewrite WfExtensionality.fix_sub_eq_ext; simpl; split_if.
        unfold add', add'_func in IHm.
        rewrite IHm.
        reflexivity.
  Qed.

  (* For comparison: *)
  Lemma add_commute : forall (n m : nat), n + m = m + n.
  Proof.
    induction n; simpl; intros.
    - induction m; simpl.
      + reflexivity.
      + rewrite <- IHm; reflexivity.
    - rewrite IHn; induction m; simpl.
      + reflexivity.
      + rewrite IHm; reflexivity.
  Qed.

  Eval simpl in (fun n (v : Vector.t nat (1 + n)) => Vector.hd v).
  Eval simpl in (fun m n (v : Vector.t nat (plus (plus 100 m) n)) => Vector.hd v).
  Eval cbv in (fun m n (v : Vector.t nat (add' 10 m)) => Vector.hd v).
  Eval compute in (fun m n (v : Vector.t nat (add' 10 m)) => Vector.hd v).

  (* Example of how add' does not play nice with simpl. *)
  Lemma Timeout : forall (m : nat) (v : Vector.t nat (add' 10 m)), Vector.hd v = Vector.hd v.
    intros.
    (* [simpl] does not terminate on my machine in under 60s. *)
    Fail Timeout 1 (*replace with your favorite bound, e.g., 60 *) simpl.
    reflexivity.
  Qed.

End DefEqPlayground.
