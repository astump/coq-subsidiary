Require Import Kinds.
Require Import Mu.
Require Import CastAlg.
Require Import Functors.

Require Import Coq.Logic.FunctionalExtensionality.

Section Init.
  
(* -------------------------------------------------------------------------------- *)
(* Assumptions *)
(* -------------------------------------------------------------------------------- *)

  Variable F : Set -> Set.
  Context {FunF : Functor F}.

(* -------------------------------------------------------------------------------- *)
(* helpers *)
(* -------------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------------- *)
(* Helper Typedefs *)
(* -------------------------------------------------------------------------------- *)

Definition FoldT(alg : KAlg)(C : Set) : Set :=
  forall (X : Set -> Set) (FunX : Functor X), alg C X -> C -> X C.

(* -------------------------------------------------------------------------------- *)
(* Algebra *)
(* -------------------------------------------------------------------------------- *)

Definition AlgF(A: KAlg)(C : Set)(X : Set -> Set) : Set :=
  forall (R : Set)
      (reveal : R -> C)        
      (fo : FoldT A R)
      (out : (R -> F R))
      (eval : R -> X R)      
      (d : F R),             
      X R.

Definition Alg := MuAlg AlgF.

Definition monoAlg : forall (A B : KAlg), CastAlg A B -> CastAlg (AlgF A) (AlgF B) :=
  fun A B f =>
    fun C X algf R reveal fo  =>
      algf R reveal (fun X xmap alg => fo X xmap (f R X alg)).

Definition castAlgId : forall (A : KAlg), CastAlg A A :=
  fun A C X d => d.
  
(* fmapId law for HO KAlg Functor *)
Lemma monoAlgId :
  forall (A : KAlg) (C : Set) (X : Set -> Set) (algf : AlgF A C X),
    monoAlg A A (castAlgId A) C X algf = algf.
  intros.
  unfold monoAlg.
  repeat (apply functional_extensionality_dep; simpl; intros).
  repeat f_equal.
Qed.

Definition rollAlg : forall {C : Set} {X : Set -> Set}, AlgF Alg C X -> Alg C X :=
  fun C X d => inMuAlg AlgF d.

Definition unrollAlg : forall {C : Set} {X : Set -> Set}, Alg C X -> AlgF Alg C X :=
  fun C X d => outMuAlg AlgF monoAlg d.

Lemma UnrollRollIso :
  forall (C : Set) (X : Set -> Set) (algf : AlgF Alg C X), unrollAlg (rollAlg algf) = algf.
  intros.
  apply monoAlgId.
Qed.

Definition antiAlg : forall {A B : Set} {X : Set -> Set}, (A -> B) -> (Alg B X) -> (Alg A X) :=
  fun A B X f alg =>
    rollAlg (fun R rev =>
               unrollAlg alg R 
                         (* building the term rev' : R -> B *)
                         (fun r => f (rev r))
            ).
  

(* -------------------------------------------------------------------------------- *)
(* building Init, our initial algebra carrier *)
(* -------------------------------------------------------------------------------- *)

Definition InitF(C : Set) := forall (X : Set -> Set) (FunX : Functor X), Alg C X -> X C.
Definition Init := Mu InitF.
    
Instance initFunc : Functor InitF :=
  {
  fmap := fun A B f initA => fun X xmap alg => fmap f (initA X xmap (antiAlg f alg));
  }.
  
Definition rollInit: InitF Init -> Init :=
  inMu InitF.

Definition unrollInit: Init -> InitF Init :=
  outMu (FunF := initFunc) InitF.

(* -------------------------------------------------------------------------------- *)
(* 
   We want to build inInit : F Init -> Init.
   to build inInit, we need to build concretizations of its abst. functions:
   - toT, fold, sfold, out.
   - promote is needed to write sfold.
*)
(* -------------------------------------------------------------------------------- *)  

Definition fold : FoldT Alg Init := fun X FunX alg d => unrollInit d X FunX alg.

Definition out : Init -> F Init :=
  fold F FunF (rollAlg (fun _ _ _ _ _ d => d)).

Definition inInit : F Init -> Init :=
  fun d => rollInit (fun X xmap alg =>
                    unrollAlg alg Init (fun x => x) fold out (fold X xmap alg) d).
  
End Init.




(* -------------------------------------------------------------------------------- *)
(* -- Common Tactics *)
(* -------------------------------------------------------------------------------- *)

Ltac simpl' :=
  simpl;
  try (repeat (rewrite monoAlgId));
  try (change (antiAlg ?F (fun x : ?T => x) ?alg)
         with alg).


          
