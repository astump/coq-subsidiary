Require Import Kinds.
Require Import Mu.
Require Import CastAlg.
Require Import Functors.

Require Import Coq.Logic.FunctionalExtensionality.

Section Subrec.
  
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
  forall (X : Set -> Set) (FunX : Functor X), alg X -> C -> X C.

(* -------------------------------------------------------------------------------- *)
(* Algebra *)
(* -------------------------------------------------------------------------------- *)

Definition AlgF(Alg: KAlg)(X : Set -> Set) : Set :=
  forall (R : Set)
      (fold : FoldT Alg R)
      (rec : R -> X R)      
      (d : F R),             
      X R.

Definition Alg : KAlg := MuAlg AlgF.

Definition monoAlg : forall (A B : KAlg), CastAlg A B -> CastAlg (AlgF A) (AlgF B) :=
  fun A B f =>
    fun X algf R fo  =>
      algf R (fun X xmap alg => fo X xmap (f X alg)).

Definition castAlgId : forall (A : KAlg), CastAlg A A :=
  fun A X d => d.
  
(* fmapId law for HO KAlg Functor *)
Lemma monoAlgId :
  forall (A : KAlg) (X : Set -> Set) (algf : AlgF A X),
    monoAlg A A (castAlgId A) X algf = algf.
  intros.
  unfold monoAlg.
  repeat (apply functional_extensionality_dep; simpl; intros).
  repeat f_equal.
Qed.

Definition rollAlg : forall {X : Set -> Set}, AlgF Alg X -> Alg X :=
  fun X d => inMuAlg AlgF d.

Definition unrollAlg : forall {X : Set -> Set}, Alg X -> AlgF Alg X :=
  fun X d => outMuAlg AlgF monoAlg d.

Lemma UnrollRollIso :
  forall (X : Set -> Set) (algf : AlgF Alg X), unrollAlg (rollAlg algf) = algf.
  intros.
  apply monoAlgId.
Qed.


Definition SubrecF(C : Set) := forall (X : Set -> Set) (FunX : Functor X), Alg X -> X C.
Definition Subrec := Mu SubrecF.
    
Instance SubrecFunctor : Functor SubrecF :=
  {
  fmap := fun A B f initA => fun X xmap alg => fmap f (initA X xmap alg);
  }.
  
Definition roll: SubrecF Subrec -> Subrec :=
  inMu SubrecF.

Definition unroll: Subrec -> SubrecF Subrec :=
  outMu (FunF := SubrecFunctor) SubrecF.

(* Characterization of roll and unroll *)
Theorem UnrollRollChar : forall (s : SubrecF Subrec),
  forall (X : Set -> Set) (FunX : Functor X) (IdF : FmapId X FunX) (alg : AlgF Alg X),
    unroll (roll s) X FunX (rollAlg alg) = s X FunX (rollAlg alg).
  intros .
  simpl.
  rewrite IdF .
  f_equal .
  Qed .
(* -------------------------------------------------------------------------------- *)
(* 
   We want to build inSubrec : F Subrec -> Subrec.
   to build inSubrec, we need to build concretizations of its abst. functions:
   - toT, fold, sfold, out.
   - promote is needed to write sfold.
*)
(* -------------------------------------------------------------------------------- *)  

Definition fold : FoldT Alg Subrec := fun X FunX alg d => unroll d X FunX alg.

Definition inn : F Subrec -> Subrec :=
  fun d => roll (fun X xmap alg =>
                    unrollAlg alg Subrec fold (fold X xmap alg) d).

Definition out{R:Set}(fo:FoldT Alg R) : R -> F R :=
  fo F FunF (rollAlg (fun _ _ _ d => d)).

(* Characterization of fold / inn *)
Theorem FoldChar : forall (X : Set -> Set) (FunX : Functor X) (IdF : FmapId X FunX)
                          (algf : AlgF Alg X) (d : F Subrec),
    fold X FunX (rollAlg algf) (inn d) =
      algf _ fold (fold X FunX (rollAlg algf)) d .
  intros .
  change (fold X FunX (rollAlg algf) (inn d)) with (unroll (roll (fun X' FunX' alg' => unrollAlg alg' _ fold (fold X' FunX' alg') d)) X FunX (rollAlg algf)) .
  rewrite UnrollRollChar .
  rewrite UnrollRollIso .
  reflexivity .
  assumption .
  Qed.
End Subrec.

Arguments rollAlg{F}{X} algf.

(* -------------------------------------------------------------------------------- *)
(* -- Common Tactics *)
(* -------------------------------------------------------------------------------- *)

Ltac simpl' :=
  simpl;
  try (repeat (rewrite monoAlgId)).


          
