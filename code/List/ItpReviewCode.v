Require Import Program Coq.Lists.List Psatz.

Local Open Scope list_scope.

Section outer.

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

Variable funny : (forall l : list A,
 (forall l0 : list A, length l0 < length l -> list (list A)) ->
 forall (hd : A) (tl : list A),
 hd :: tl = l -> length (snd (break tl)) < length l).

  Program Fixpoint wordsBy (l:list A) {measure (Datatypes.length l)} : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsBy tl
        else
          match break tl with
            (p,s) =>
              (hd::p)::(wordsBy s)
          end
    end.
  Next Obligation.
    destruct (break tl) eqn:e.
    inversion Heq_anonymous.
simpl. apply Lt.le_lt_n_Sm. change l0 with (snd (l,l0)). rewrite <- e . apply span_snd_smaller.
  Qed.

End Span.

Section test.

Arguments wordsBy {A}.

Print wordsBy.

Eval compute in (wordsBy (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Definition t1 := repeat 0 1200.

Eval compute in (wordsBy (Nat.eqb 0) t1).
Eval compute in (wordsBy (Nat.eqb 0) (t1 ++ 1 :: 1 :: 2 :: (0:: 1 :: 3 :: 5 :: 0 :: nil))).


(*
Print wordsBy.
Print wordsBy_obligation_3.
*)