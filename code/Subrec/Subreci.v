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
    fun d => forall (X : kMo -> kMo) (xmap : fmapiT Subrec X), alg C X -> C d -> X C d.

(* -------------------------------------------------------------------------------- *)
(* Algebra *)
(* -------------------------------------------------------------------------------- *)


Definition AlgF(A: KAlgi)(C : kMo)(X : kMo -> kMo) : Set :=
  forall (R : kMo)
    (reveal : (forall (d : Subrec), R d -> C d))        
    (fo : (forall (d : Subrec), FoldTi A R d))
    (out : (forall (d : Subrec), (R d -> Fi R d)))
    (ih : (forall (d : Subrec), R d -> X R d))
    (d : Subrec),
    Fi R d -> X R d.

Definition Algi := MuAlgi Subrec AlgF.

Definition monoAlgi : forall (A B : KAlgi),
    CastAlgi Subrec A B ->
    CastAlgi Subrec (AlgF A) (AlgF B) :=
  fun A B cAB =>
    fun C X algf R reveal fo  =>
      algf R reveal (fun i' X xmap alg => fo i' X xmap (cAB _ _ alg)).

Definition rollAlgi : forall {C : kMo} {X : kMo -> kMo}, AlgF Algi C X -> Algi C X :=
 fun C X i => inMuAlgi Subrec AlgF i.

Definition unrollAlgi : forall {C : kMo} {X : kMo -> kMo}, Algi C X -> AlgF Algi C X :=
  fun C X => outMuAlgi Subrec AlgF monoAlgi.

Definition antiAlgi : forall {A B : kMo} {X : kMo -> kMo},
    (forall (i : Subrec), (A i -> B i)) -> Algi B X -> Algi A X :=
  fun A B X f alg =>
    rollAlgi (fun R reveal => unrollAlgi alg R (fun d rd => f d (reveal d rd))).

(* -------------------------------------------------------------------------------- *)
(* ... *)
(* -------------------------------------------------------------------------------- *)

Definition SubrecFi(C : kMo) : kMo := fun d => forall (X : kMo -> kMo) (xmap : fmapiT Subrec X), Algi C X -> X C d.
Definition Subreci := Mui Subrec SubrecFi.

Definition SubrecFmapi : fmapiT Subrec SubrecFi.
  intros A B f i d.
  intros X xmap alg.
  unfold SubrecFi in d.
  exact (xmap A B f i (d X xmap (antiAlgi f alg))).
Defined.

Definition rolli :=
  inMui Subrec SubrecFi.

Definition unrolli :=
  outMui Subrec SubrecFi SubrecFmapi.

(* -------------------------------------------------------------------------------- *)
(* Building toSubreci. *)
(* -------------------------------------------------------------------------------- *)  


Definition foldi(i : Subrec) : FoldTi Algi Subreci i := fun X xmap alg d => unrolli i d X xmap alg.

Definition outi(i :Subrec) : Subreci i -> Fi Subreci i :=
  foldi i Fi FiMap
            (rollAlgi
               (fun R rev fo out ih i' df => df)).


Definition inni(i : Subrec)(fd : Fi Subreci i) : Subreci i :=
  rolli i 
            (fun X xmap alg =>
               let reveal := fun d1 x => x in
               let IH := fun i1 d => unrolli i1 d X xmap alg in
               unrollAlgi alg Subreci reveal foldi outi IH i fd
            ).
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

