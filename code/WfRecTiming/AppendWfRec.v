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

  Print appendWf_func.
  Print appendWf_func_obligation_1.

Definition appendWf_func_obligation_1'      : forall l1 : list A,
       (forall l2 : list A, list A -> length l2 < length l1 -> list A) ->
       forall (hd : A) (tl : list A), hd :: tl = l1 -> length tl < length l1 .
exact (fun (l1 : list A)
  (appendWf : forall l2 : list A, list A -> length l2 < length l1 -> list A)
  (hd : A) (tl : list A) (Heq_l1 : hd :: tl = l1) =>
eq_ind (hd :: tl)
  (fun l2 : list A =>
   (forall l3 : list A, list A -> length l3 < length l2 -> list A) ->
   length tl < length l2)
  (fun
     _ : forall l2 : list A,
         list A -> length l2 < length (hd :: tl) -> list A =>
   le_n (length (hd :: tl))) l1 Heq_l1 appendWf).
Qed.

Print appendWf.

Definition appendWf_func'      : forall recarg : {_ : list A & list A},
       let l1 := projT1 recarg in let l2 := projT2 recarg in list A := 
Fix_sub {_ : list A & list A}
  (MR lt
     (fun recarg : {_ : list A & list A} =>
      let l1 := projT1 recarg in let l2 := projT2 recarg in length l1))
  appendWf_func_obligation_2
  (fun recarg : {_ : list A & list A} =>
   let l1 := projT1 recarg in let l2 := projT2 recarg in list A)
  (fun (recarg : {_ : list A & list A})
     (appendWf' : forall
                    recarg' : {recarg' : {_ : list A & list A}
                              | (let l1 := projT1 recarg' in
                                 let l2 := projT2 recarg' in length l1) <
                                (let l1 := projT1 recarg in
                                 let l2 := projT2 recarg in length l1)},
                  let l1 := projT1 (` recarg') in
                  let l2 := projT2 (` recarg') in list A) =>
   let l1 := projT1 recarg in
   let l2 := projT2 recarg in
   let appendWf :=
     fun (l3 l4 : list A) (recproof : length l3 < length l1) =>
     appendWf'
       (exist
          (fun recarg' : {_ : list A & list A} =>
           (let l5 := projT1 recarg' in let l6 := projT2 recarg' in length l5) <
           (let l5 := projT1 recarg in let l6 := projT2 recarg in length l5))
          (existT (fun _ : list A => list A) l3 l4) recproof) in
   let program_branch_0 := fun _ : nil = l1 => l2 in
   let program_branch_1 :=
     fun (hd : A) (tl : list A) (Heq_l1 : hd :: tl = l1) =>
     hd
     :: appendWf tl l2
          ((fun (l3 _ : list A)
              (appendWf0 : forall l5 : list A,
                           list A -> length l5 < length l3 -> list A)
              (hd0 : A) (tl0 : list A) (Heq_l2 : hd0 :: tl0 = l3) =>
            appendWf_func_obligation_1' l3 appendWf0 hd0 tl0 Heq_l2) l1 l2
             appendWf hd tl Heq_l1) in
   match l1 as l1' return (l1' = l1 -> list A) with
   | nil => program_branch_0
   | hd :: tl => program_branch_1 hd tl
   end eq_refl).

Definition appendWf1 : list A -> list A -> list A := 
fun l1 l2 : list A => appendWf_func' (existT (fun _ : list A => list A) l1 l2).
     

(*
  Program Fixpoint appendMy(l1 l2:list A) {measure (Datatypes.length l1) mylt} : list A :=
    match l1 with
    | nil => l2
    | hd :: tl =>
        hd :: (appendWf tl l2)
    end.
Next Obligation.
intro a.
unfold MR.
apply Acc_intro.
intros y uy.
destruct uy.
*)

End AppendWfRec.

Definition appendSl{A : Type}(l1 l2 : list A) : list A := appendSlh A l2 l1.
Arguments appendWf{A}.
Arguments appendWf1{A}.

Eval compute in (length (appendWf1 (10 :: nil) (repeat 1 10))).

(*
Section test.
  
Eval compute in (appendSl (10 :: nil) (repeat 1 2)).
Eval compute in (length (appendSl (10 :: nil) (repeat 1 500))).
Eval compute in (length (appendWf (10 :: nil) (repeat 1 1000))).

Print Fix_sub.
Print appendSl.
Print appendSl_obligation_1.

End test.*)