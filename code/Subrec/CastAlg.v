Require Import Kinds.

(* -------------------------------------------------------------------------------- *)
(* 
   CastAlg: Cast from one algebra to another, parametrically over any carrier C
   and Endofunctor X.

*)
(* -------------------------------------------------------------------------------- *)

Definition CastAlg(alg1 alg2 : KAlg) :=
  forall (X : Set -> Set), alg1 X -> alg2 X.

