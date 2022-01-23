Require Import Kinds.
Require Import Mu.
Require Import CastAlg.
Require Import Functors.
Require Import Subrec.

Require Import Coq.Program.Basics.

Variable F : Set -> Set.
Context {FunF : Functor F}.

Section Schemes .

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

  Section CofreeRecursiveComonad.

    Definition MRec{R : Set}(fo : FoldT (Alg F) R) : Set :=
      forall (C : Set), (forall (Y : Set), (Y -> C) -> (Y -> R) -> F Y -> C) -> R -> C .

    Definition mrec{R : Set}(fo : FoldT (Alg F) R) : MRec fo :=
      fun C psi x => fo _ _ (rollAlg (fun R' re' fo' rec' xs => psi R' rec' re' xs)) x .

    Definition Update : Set :=
      forall {C Y : Set},
        (forall {C' : Set}, (forall {Y' : Set}, (Y' -> C') -> (Y' -> Y) -> F Y' -> C') -> Y -> C')
        -> (Y -> C)
        -> (forall {C' : Set}, (forall {Y' : Set}, (Y' -> C) -> (Y' -> C') -> F Y' -> C') -> Y -> C') .

    Definition update : Update :=
      fun C Y theta g C' psi => theta _ (fun Y' de io => psi _ (compose g io) de) .

    Definition RCRSubAlg (C Y : Set) :=
      (forall (C' : Set),
          (forall (Y' : Set), (Y' -> C) -> (Y' -> C') -> F Y' -> C') -> Y -> C') .
    
    Definition RCRAlg (C : Set) : Set :=
      (forall (Y : Set), (Y -> C) -> RCRSubAlg C Y -> F Y -> C) .


    Definition Miter2 : Set :=
      forall (C : Set), RCRAlg C -> Subrec F -> C .

    Definition miter2 : Miter2 :=
      fun C psi x =>
        fold F _ _
             (rollAlg
                (fun R re fo rec xs =>
                   psi R rec (update C R (mrec fo) rec) xs))
             x .
    Theorem MIter2Char (X : Set) (alg : RCRAlg X) (xs : F (Subrec F)) :
      miter2 X alg (inn F xs) = alg _ (miter2 X alg) (update _ _ (mrec (fold F)) (miter2 X alg)) xs.
      change (miter2 X alg (inn F xs))
        with (fold F _ _ (rollAlg
                            (fun R re fo rec xs =>
                               alg R rec (update _ _ (mrec fo) rec) xs)) (inn F xs)) .
      rewrite (FoldChar F) .
      reflexivity .
      apply FmapIdConst .
    Qed .

  End CofreeRecursiveComonad .

End Schemes .
