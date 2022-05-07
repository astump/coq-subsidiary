Require Import Program Coq.Lists.List Psatz.
Require Import SmallerListWf.
Local Open Scope list_scope.
Require Import Nat.
Require Import Arith.Wf_nat.

Fixpoint mid{A : Type}(n : nat)(x : A) : A :=
  match n with
    O => x
  | S n => id (mid n x)
  end.
  
Inductive mylt : nat -> nat -> Prop := mkMyle : forall n m : nat , n < m -> mylt n m.

Section AppendWfRec.

  Variable A : Type.
  Variable l2 : list A.

  Program Fixpoint appendSlh(l1:list A) {measure l1 (smallerList A)} : list A :=
    match l1 with
    | nil => l2
    | hd :: tl =>
        hd :: (appendSlh tl)
    end.
  Next Obligation.
    exact (smallerListTail A tl hd).
  Qed.
  Next Obligation.
    unfold MR.
    exact (smallerListWf A).  
  Defined.

  Program Fixpoint appendWf(l1 l2:list A) {measure (Datatypes.length l1)} : list A :=
    match l1 with
    | nil => l2
    | hd :: tl =>
        hd :: (appendWf tl l2)
    end.

End AppendWfRec.

Definition appendSl{A : Type}(l1 l2 : list A) : list A := appendSlh A l2 l1.
Arguments appendWf{A}.

Eval compute in (length (appendWf (repeat 1 10) (10 :: nil))).

(*
Section test.
  
Eval compute in (appendSl (10 :: nil) (repeat 1 2)).
Eval compute in (length (appendSl (10 :: nil) (repeat 1 500))).
Eval compute in (length (appendWf (10 :: nil) (repeat 1 1000))).

Print Fix_sub.
Print appendSl.
Print appendSl_obligation_1.

End test.*)