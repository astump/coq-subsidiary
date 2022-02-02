Require Import Kinds.
Require Import Mu.
Require Import Mui.
Require Import Functors.
Require Import CastAlg.
Require Import Subrec.
  
Section Subreci.
  
(* -------------------------------------------------------------------------------- *)
(* Assumptions *)
(* -------------------------------------------------------------------------------- *)
  Variable F : Set -> Set.

  Context {FunF : Functor F}.

  Definition Subrec := Subrec F.
  Definition KAlgi := KAlgi Subrec.
  Definition kMo := kMo Subrec.

  Variable Fi : kMo -> kMo.
  
  Class DepF :=
    {    
    (* Assumptions *)
    FiMap : fmapiT Subrec Fi;
    }.

  Context {depf : DepF}.  
 
(* -------------------------------------------------------------------------------- *)
(* helpers *)
(* -------------------------------------------------------------------------------- *)

  Definition Consti(R: kMo) : kMo -> kMo := fun _ d => R d.
  Definition FunConsti(R : kMo) : fmapiT Subrec (Consti R) :=
    fun A B f i xs => xs.

(* -------------------------------------------------------------------------------- *)
(* Helper Typedefs *)
(* -------------------------------------------------------------------------------- *)
  
  Definition FoldTi(alg : KAlgi)(C : kMo) : kMo :=
    fun d => forall (X : kMo -> kMo) (xmap : fmapiT Subrec X), alg X -> C d -> X C d.

(* -------------------------------------------------------------------------------- *)
(* Algebra *)
(* -------------------------------------------------------------------------------- *)


Definition AlgFi(A: KAlgi)(X : kMo -> kMo) : Set :=
  forall (R : kMo)
    (fo : (forall (d : Subrec), FoldTi A R d))
    (ih : (forall (d : Subrec), R d -> X R d))
    (d : Subrec),
    Fi R d -> X R d.

Definition Algi := MuAlgi Subrec AlgFi.

Definition monoAlgi : forall (A B : KAlgi),
    CastAlgi Subrec A B ->
    CastAlgi Subrec (AlgFi A) (AlgFi B) :=
  fun A B cAB =>
    fun X algf R fo  =>
      algf R (fun i' X xmap alg => fo i' X xmap (cAB _ alg)).

Definition rollAlgi : forall {X : kMo -> kMo}, AlgFi Algi X -> Algi X :=
 fun X i => inMuAlgi Subrec AlgFi i.

Definition unrollAlgi : forall {X : kMo -> kMo}, Algi X -> AlgFi Algi X :=
  fun X => outMuAlgi Subrec AlgFi monoAlgi.

(* -------------------------------------------------------------------------------- *)
(* ... *)
(* -------------------------------------------------------------------------------- *)

Definition SubrecFi(C : kMo) : kMo := fun d => forall (X : kMo -> kMo) (xmap : fmapiT Subrec X), Algi X -> X C d.
Definition Subreci := Mui Subrec SubrecFi.

Definition SubrecFmapi : fmapiT Subrec SubrecFi.
  intros A B f i d.
  intros X xmap alg.
  unfold SubrecFi in d.
  exact (xmap A B f i (d X xmap alg)).
Defined.

Definition rolli :=
  inMui Subrec SubrecFi.

Definition unrolli :=
  outMui Subrec SubrecFi SubrecFmapi.

(* -------------------------------------------------------------------------------- *)
(* Building toSubreci. *)
(* -------------------------------------------------------------------------------- *)  


Definition foldi(i : Subrec) : FoldTi Algi Subreci i := fun X xmap alg d => unrolli i d X xmap alg.


Definition inni(i : Subrec)(fd : Fi Subreci i) : Subreci i :=
  rolli i 
            (fun X xmap alg =>
               let IH := fun i1 d => unrolli i1 d X xmap alg in
               unrollAlgi alg Subreci foldi IH i fd
            ).

Definition outi{R:Subrec -> Prop}
           (foi : forall i : Subrec, FoldTi Algi R i)
           (i :Subrec) : R i -> Fi R i :=
  foi i Fi FiMap
            (rollAlgi
               (fun R fo ih i' df => df)).



End Subreci.

(* Make F implicit for all terms after Subrec decl. *)
Arguments foldi {F} {Fi}.
Arguments Consti {F}.
Arguments FunConsti {F}.
Arguments rollAlgi {F} {Fi}.
Arguments unrollAlgi {F} {Fi}.
Arguments rolli {F} {Fi}.
Arguments unrolli {F} {Fi}.
Arguments inni {F} {Fi}.

