(* substitute a number and an append function for the capitalized names *)
Require Import AppendWfRec.

Require Import Lists.List.

Definition t1 := repeat 0 NUM.

Eval compute in (length (APP t1 nil)).



