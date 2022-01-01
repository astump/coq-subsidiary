Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Require Import List.Repeat.

Import ListNotations.

Section Rld.
Context {A : Set}.

Fixpoint rld(xs : list (nat * A)) : list A :=
  match xs with
  | [] => []
  | (n, v) :: tl => repeat n v ++ rld tl
  end.

End Rld.