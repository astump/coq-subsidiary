Require Import Kinds.
Require Import Mu.
Require Import CastAlg.
Require Import Functors.
Require Import Subrec.

Require Import Coq.Program.Basics.

Section Schemes .

  Variable F : Set -> Set.
  Context {FunF : Functor F}.

  Section CourseOfValues.

    Definition MCVAlg (X : Set) :=
      forall (R : Set), (R -> F R) -> (R -> X) -> F R -> X .

    Definition MCVIter : Set :=
      forall (X : Set), MCVAlg X -> Subrec F -> X .

    Definition mcviter : MCVIter :=
      fun X alg x => fold F _ _ (rollAlg (fun R re fo rec xs => alg R (out F fo) rec xs)) x .
   
    Theorem MCVIterChar (X : Set) (alg : MCVAlg X) (xs : F (Subrec F)) :
      mcviter X alg (inn F xs) = alg _ (out F (fold F)) (mcviter _ alg) xs.
      change (mcviter X alg (inn F xs))
        with (fold F _ _ (rollAlg (fun R re fo rec xs => alg R (out F fo) rec xs)) (inn F xs)) .
      rewrite (FoldChar F) .
      reflexivity .
      apply FmapIdConst .
      Qed .

  End CourseOfValues .

End Schemes .

(* Section CofreeRecursiveComonad. *)

(*     Definition MRec : Set := *)
(*       forall (C : Set), (forall (Y : Set), (Y -> C) -> (Y -> Subrec F) -> F Y -> C) -> Subrec F -> C . *)

(*     Definition mrec : MRec := *)
(*       fun C psi x => fold F _ _ (rollAlg (fun R re fo rec xs => psi R rec re xs)) x . *)

(*     Definition Update : Set := *)
(*       forall {C Y : Set}, *)
(*         (forall {C' : Set}, (forall {Y' : Set}, (Y' -> C') -> (Y' -> Subrec F) -> F Y' -> C') -> Y -> C') *)
(*         -> (Y -> C) *)
(*         -> (forall {C' : Set}, (forall {Y' : Set}, (Y' -> C) -> (Y' -> C') -> F Y' -> C') -> Y -> C') . *)

(*     Definition update : Update := *)
(*       fun C Y theta g C' psi => theta _ (fun Y' de io => psi _ (compose g io) de) . *)

(*     Definition Miter2 : Set := *)
(*       forall (C : Set), *)
(*         (forall (Y : Set), *)
(*             (Y -> C) *)
(*             -> (forall (C' : Set), *)
(*                    (forall (Y' : Set), (Y' -> C) -> (Y' -> C') -> F Y' -> C') -> Y -> C') *)
(*             -> F Y -> C) *)
(*         -> Subrec F -> C . *)

(*     Definition miter2 : Miter2 := *)
(*       fun C psi x => *)
(*         fold F _ _ *)
(*              (rollAlg (fun R re fo rec xs => *)
(*                          psi R rec *)
(*                              (fun C' theta x' => update C R (fun C'' psi'' x'' => mrec C'' psi'' (re x'')) _ _ _ _) *)
(*                              xs)) *)
(*              x . *)
