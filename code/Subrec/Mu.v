Require Import Kinds.
Require Import CastAlg.
Require Import Functors.
Require Import Coq.Setoids.Setoid.

 
Section Mu.

  Context (F : Set -> Set)
          {FunF : Functor F}
          {fmapId : forall (A : Set)(d : F A), fmap (fun x => x) d = d}.   

  Definition MAlgebra
             (A : Set) :=
    forall (R : Set), (R -> A) -> F R -> A.

  Inductive Mu : Set := 
    mu : MAlgebra Mu.

  Definition inMu(d : F Mu) : Mu :=
    mu Mu (fun x => x) d.

  Definition outMu(m : Mu) : F Mu :=
    match m with
    | mu A r d => fmap r d
    end.

  Lemma outIn(d : F Mu) : outMu (inMu d) = d.
    simpl.
    rewrite fmapId.
    reflexivity.
  Qed.

  Definition IndMu(m : Mu) : Set :=
    forall X : Mu -> Set,
      (forall(R:Set)(reveal : R -> Mu),
          (forall r : R, X (reveal r)) ->
          forall d : F R ,
            X (mu R reveal d))->
      X m.

  Fixpoint Mu_fold
           {A : Set}
           (alg : MAlgebra A)
           (m : Mu)
    {struct m} : A :=
    match m with
      mu A reveal d => alg _ (fun r => Mu_fold alg (reveal r) ) d
    end.
    
  Definition normalize_Mu (m : Mu) : Mu :=
    Mu_fold (fun R rec fr => inMu (fmap rec fr)) m.

  Definition Mu_equiv (m1 m2 : Mu) : Prop := normalize_Mu m1 = normalize_Mu m2.

  Lemma Mu_equiv_refl : Reflexive Mu_equiv.
    unfold Reflexive; reflexivity.
  Qed.

  Lemma Mu_equiv_sym : Symmetric Mu_equiv.
    unfold Symmetric; symmetry; eauto.
  Qed.

  Lemma Mu_equiv_trans : Transitive Mu_equiv.
    unfold Transitive; etransitivity; eauto.
  Qed.

  #[global] Add Relation Mu Mu_equiv
      reflexivity proved by Mu_equiv_refl
      symmetry proved by Mu_equiv_sym
      transitivity proved by Mu_equiv_trans
    as Mu_equiv_rel.

  Infix "≈" := Mu_equiv (at level 90).
  
End Mu.

(* -------------------------------------------------------------------------------- *)
(* 
   Higher-ordered Mu over KAlg .
   This permits non-strictly positive occurrences of Alg in defining
   Alg via their (higher ordered) functors AlgF.
*)
(* -------------------------------------------------------------------------------- *)


Section MuAlg.

  Variable F : KAlg -> KAlg.
  Variable algMap : forall {A B : KAlg}, CastAlg A B -> CastAlg (F A) (F B). 


  Inductive MuAlg : KAlg := 
  muAlg : forall A : KAlg,
    (forall (C : Set) (X : Set -> Set), A C X -> MuAlg C X) ->
    forall (C : Set) (X : Set -> Set), F A C X -> MuAlg C X.

  Definition inMuAlg {C : Set} {X : Set -> Set} (d : (F MuAlg) C X) : MuAlg C X :=
    muAlg MuAlg (fun C X x => x) C X d.

  
  Definition outMuAlg{C : Set} {X : Set -> Set} (v : MuAlg C X) : (F MuAlg) C X :=
    match v with
    | muAlg A r C1 X1 d => algMap r C1 X1 d
    end.
End MuAlg.
