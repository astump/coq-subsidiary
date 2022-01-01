Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Import ListNotations.

Section Repeat.
Context {A : Set}.

Fixpoint repeat(count : nat) (v : A) : list A :=
  match count with
  | 0   => []
  | S n =>  v :: (repeat n v)
  end.

Lemma hopRepeat : forall (n : nat)(a : A)(xs : list A),
    a :: repeat n a ++ xs = repeat n a ++ a :: xs.
  intros. induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

End Repeat.