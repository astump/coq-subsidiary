Require Import Kinds.
Require Import Mu.
Require Import Mui.
Require Import Functors.
Require Import CastAlg.
Require Import Init.
  
Section Initi.
  
(* -------------------------------------------------------------------------------- *)
(* Assumptions *)
(* -------------------------------------------------------------------------------- *)
  Variable F : Set -> Set.

  Context {FunF : Functor F}.

  (* currying defs from Init.v with F and (Init F) *)
  Definition Init := Init F.
  Definition KAlgi := KAlgi Init.
  Definition kMo := kMo Init.

  Variable Fi : kMo -> kMo.
  
  Class DepF :=
    {    
    (* Assumptions *)
    FiMap : fmapiT Init Fi;
    }.

  Context {depf : DepF}.  
 
(* -------------------------------------------------------------------------------- *)
(* helpers *)
(* -------------------------------------------------------------------------------- *)

  Definition Consti(R: kMo) : kMo -> kMo := fun _ d => R d.
  Definition constimap(R : kMo) : fmapiT Init (Consti R) :=
    fun A B f i xs => xs.

(* -------------------------------------------------------------------------------- *)
(* Helper Typedefs *)
(* -------------------------------------------------------------------------------- *)
  
  Definition FoldTi(alg : KAlgi)(C : kMo) : kMo :=
    fun d => forall (X : kMo -> kMo) (xmap : fmapiT Init X), alg C X -> C d -> X C d.

(* -------------------------------------------------------------------------------- *)
(* Algebra *)
(* -------------------------------------------------------------------------------- *)


Definition AlgF(A: KAlgi)(C : kMo)(X : kMo -> kMo) : Set :=
  forall (R : kMo)
    (reveal : (forall (d : Init), R d -> C d))        
    (fo : (forall (d : Init), FoldTi A R d))
    (out : (forall (d : Init), (R d -> Fi R d)))
    (ih : (forall (d : Init), R d -> X R d))
    (d : Init),
    Fi R d -> X R d.

Definition Algi := MuAlgi Init AlgF.

Definition monoAlgi : forall (A B : KAlgi),
    CastAlgi Init A B ->
    CastAlgi Init (AlgF A) (AlgF B) :=
  fun A B cAB =>
    fun C X algf R reveal fo  =>
      algf R reveal (fun i' X xmap alg => fo i' X xmap (cAB _ _ alg)).

Definition rollAlgi : forall {C : kMo} {X : kMo -> kMo}, AlgF Algi C X -> Algi C X :=
 fun C X i => inMuAlgi Init AlgF i.

Definition unrollAlgi : forall {C : kMo} {X : kMo -> kMo}, Algi C X -> AlgF Algi C X :=
  fun C X => outMuAlgi Init AlgF monoAlgi.

Definition antiAlgi : forall {A B : kMo} {X : kMo -> kMo},
    (forall (i : Init), (A i -> B i)) -> Algi B X -> Algi A X :=
  fun A B X f alg =>
    rollAlgi (fun R reveal => unrollAlgi alg R (fun d rd => f d (reveal d rd))).

(* -------------------------------------------------------------------------------- *)
(* ... *)
(* -------------------------------------------------------------------------------- *)

Definition InitFi(C : kMo) : kMo := fun d => forall (X : kMo -> kMo) (xmap : fmapiT Init X), Algi C X -> X C d.
Definition Initi := Mui Init InitFi.

Definition InitFmapi : fmapiT Init InitFi.
  intros A B f i d.
  intros X xmap alg.
  unfold InitFi in d.
  exact (xmap A B f i (d X xmap (antiAlgi f alg))).
Defined.

Definition rollIniti :=
  inMui Init InitFi.

Definition unrollIniti :=
  outMui Init InitFi InitFmapi.

(* -------------------------------------------------------------------------------- *)
(* Building toIniti. *)
(* -------------------------------------------------------------------------------- *)  


Definition foldi(i : Init) : FoldTi Algi Initi i := fun X xmap alg d => unrollIniti i d X xmap alg.

Definition outi(i :Init) : Initi i -> Fi Initi i :=
  foldi i Fi FiMap
            (rollAlgi
               (fun R rev fo out ih i' df => df)).


Definition inIniti(i : Init)(fd : Fi Initi i) : Initi i :=
  rollIniti i 
            (fun X xmap alg =>
               let reveal := fun d1 x => x in
               let IH := fun i1 d => unrollIniti i1 d X xmap alg in
               unrollAlgi alg Initi reveal foldi outi IH i fd
            ).
End Initi.

(* Make F implicit for all terms after Init decl. *)
Arguments foldi {F} {Fi}.
Arguments Consti {F}.
Arguments constimap {F}.
Arguments rollAlgi {F} {Fi}.
Arguments unrollAlgi {F} {Fi}.
Arguments rollIniti {F} {Fi}.
Arguments unrollIniti {F} {Fi}.
Arguments inIniti {F} {Fi}.

