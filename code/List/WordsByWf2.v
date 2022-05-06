(* try using binary nats as a measure *)

Require Import Program Coq.Lists.List Psatz .

Require Coq.Bool.Bool.

Local Open Scope list_scope.

(*
Theorem wf_lt1 : well_founded lt.
Proof.
  assert (H : forall n (a:nat), a < n -> Acc lt a).
  { induction n.
    - intros; absurd (a < 0); auto with arith.
    - intros a Ha. apply Acc_intro. unfold lt at 1. intros b Hb.
      apply IHn. apply Nat.lt_le_trans with a; auto with arith. }
  intros a. apply (H (S a)). auto with arith.
Defined.
*)

Definition bnat := list bool.

Lemma bnatInd : 
  forall(P : bnat -> Prop),
    P nil ->
    (forall(bs : bnat),
        P bs -> P (false :: bs)) ->
    (forall(bs : bnat),
        P (false :: bs) -> P (true :: bs)) ->
    forall(bs : bnat),
      P bs.
  intros P base step1 step2 bs.
  induction bs.  
  - exact base.
  - assert (H : P (false :: bs)).
    -- apply step1.
       exact IHbs.
    -- destruct a.
       --- apply step2; exact H.
       --- exact H.
  Defined.

(* least significant bit earlier in list *)
Inductive BnatLt : bnat -> bnat -> Prop :=
  Start : forall(hi:bnat), BnatLt (false :: hi) (true :: hi)
| Ext1 : forall(b:bool)(bs1 bs2:bnat), BnatLt bs1 bs2 -> BnatLt (b :: bs1) bs2
| Ext2 : forall(b:bool)(bs1 bs2:bnat), BnatLt bs1 bs2 -> BnatLt bs1 (b :: bs2).

Lemma bnatLtNil : forall (b : bnat), BnatLt b nil -> False.
intro b; induction b; intro p; inversion p.
exact (IHb H2).
Qed.

Fixpoint bnatLtFalse(x y : bnat)(p : BnatLt x (false :: y)) : BnatLt x y.
  inversion p.
  - apply Ext1.
    apply bnatLtFalse; assumption.
  - assumption.
Qed.

Lemma bnatLtTrans : forall(x y z : bnat), BnatLt x y -> BnatLt y z -> BnatLt x z.
  Admitted.

Lemma bnatLtTransTrue : forall(x y z : bnat), BnatLt x y -> BnatLt y (true :: z) -> BnatLt x (false :: z).
  Admitted.

Section offun.
  (* similar to Coq.Arith.Wf_nat *)
  Variable A : Set.
  Variable f : A -> bnat.
  Definition ltof(a b : A) := BnatLt (f a) (f b).
  
Lemma bnatLtLem : forall (y x : A) , ltof x y -> Acc ltof x.
  assert (Q : forall (n : bnat)(a : A), BnatLt (f a) n -> Acc ltof a).
  - induction n using bnatInd; intros x p.
    -- contradiction (bnatLtNil (f x) p).
    -- apply Acc_intro; intros z q.
       apply IHn.    
       set (i := bnatLtFalse (f x) n p).
       unfold ltof in q.
       set (t := bnatLtTrans (f z) (f x) n q i).
       assumption.
  -- apply Acc_intro; intros z q.
     apply IHn.
     unfold ltof in q.
     exact (bnatLtTransTrue (f z) (f x) n q p).
  - intros y x p.
    exact (Q (f y) x p).
Defined.

Theorem bnatLtWf : well_founded ltof.
  intro a.
  apply Acc_intro.
  exact (bnatLtLem a).
Defined.

End offun.  

Fixpoint bnatSucc(bs : bnat) : bnat :=
  match bs with
    nil => true :: nil
  | b :: bs' =>
    if b then
      false :: bnatSucc bs'
    else
      true :: bs'
  end.

Fixpoint toBnat(n : nat) : bnat :=
  match n with
    O => false :: nil
  | S p => bnatSucc (toBnat p)
  end.

Section Span.

  Variable A : Set.

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

  Definition listBnatLt(l1 l2 : list A) : Prop := BnatLt (toBnat (Datatypes.length l1)) (toBnat (Datatypes.length l2)).

  Program Fixpoint wordsByWf (l:list A) {measure l listBnatLt} : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByWf tl
        else
          (hd::(fst (break tl)))::(wordsByWf (snd (break tl)))
    end.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  unfold MR.
  unfold well_founded.
  exact (bnatLtWf (list A) (fun x => toBnat (length x))).
  Defined.

End Span.

Arguments wordsByWf {A} p l.

Eval compute in (wordsByWf (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Definition t1 := repeat 0 1000.

(* blows the stack:
Eval compute in (wordsByWf (Nat.eqb 0) (t1 ++ 1 :: 1 :: 2 :: (t1 ++ 1 :: 3 :: 5 :: 0 :: nil))).
*)

(*
Print wordsByWf.
Print wordsByWf_obligation_3.
*)