Require Import Program Coq.Lists.List Psatz.

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

  Program Fixpoint wordsByWf (l:list A) {measure (Datatypes.length l)} : list (list A) :=
    match l with
    | nil => nil
    | hd::tl =>
        if p hd then
          wordsByWf tl
        else
          (hd::(fst (break tl)))::(wordsByWf (snd (break tl)))
    end.
  Next Obligation.
    simpl. now apply Lt.le_lt_n_Sm, span_snd_smaller.
  Defined.

  Print wordsByWf_obligation_3.

End Span.

Arguments wordsByWf {A} p l.

(*
Eval compute in (wordsByWf (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

Definition t1 := repeat 0 1000.

Eval compute in (wordsByWf (Nat.eqb 0) (t1 ++ 1 :: 1 :: 2 :: (t1 ++ 1 :: 3 :: 5 :: 0 :: nil))).
*)

(*
Print wordsByWf.
Print wordsByWf_obligation_3.
*)