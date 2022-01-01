Require Import Coq.Sorting.Sorted.
Require Import ExtraLib.

Section Pd.

Context {A : Set}(eqb : A -> A -> bool).

Definition PairwiseDistinct := LocallySorted (liftRel eqb).

End Pd.

        