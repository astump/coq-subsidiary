Require Import Kinds.

(* -------------------------------------------------------------------------------- *)
(* Mu over propositions. *)
(* -------------------------------------------------------------------------------- *)
Section Defs.
    Variable I : Set.
    Definition kMo := I -> Prop.
    Definition KSAlgi := kMo -> kMo -> (kMo -> kMo) -> Set.
    Definition KAlgi := kMo -> (kMo -> kMo) -> Set.

    Definition CastSAlgi(salg1 salg2 : KSAlgi) := 
      forall (S : kMo) (R : kMo) (X : kMo -> kMo), salg1 S R X -> salg2 S R X.

    Definition CastAlgi(alg1 alg2 : KAlgi) := 
      forall (R : kMo) (X : kMo -> kMo), alg1 R X -> alg2 R X.

    Section Muis.
      Variable F : kMo -> kMo.
      Definition fmapiT : Prop := forall(A B : kMo), (forall i : I , A i -> B i) -> forall (i : I), F A i -> F B i.
      
      Variable fmapi : fmapiT.

      Inductive Mui : kMo :=
        mui : forall A : kMo , (forall i : I , A i -> Mui i) -> forall (i : I) , F A i -> Mui i.

      Definition inMui(i : I)(d : F Mui i) : Mui i :=
        mui Mui (fun X x => x) i d.

      Definition outMui(i : I)(m : Mui i) : F Mui i :=
        match m with
        | mui A r i d => fmapi A Mui r i d
        end.

    End Muis.

    (* -------------------------------------------------------------------------------- *)
    (* 
   Higher-ordered Mu over KAlg and KSAlg.
   This permits non-strictly positive occurrences of SAlg and Alg in defining
   SAlg and Alg via their (higher ordered) functors SAlgF and AlgF.
     *)
    (* -------------------------------------------------------------------------------- *)

    Section MuSAlg.
      Variable F : KSAlgi -> KSAlgi.
      Variable salgMap : forall {A B : KSAlgi}, CastSAlgi A B -> CastSAlgi (F A) (F B).

      Inductive MuSAlgi : KSAlgi := 
        muSAlg : forall A : KSAlgi,
          (forall (S : kMo) (C : kMo) (X : kMo -> kMo), A S C X -> MuSAlgi S C X) ->
          forall (S : kMo) (C : kMo) (X : kMo -> kMo), F A S C X -> MuSAlgi S C X.

      Definition inMuSAlgi {S : kMo} {C : kMo} {X : kMo -> kMo} (d: (F MuSAlgi) S C X) : MuSAlgi S C X :=
        muSAlg MuSAlgi (fun S C X d' => d') S C X d.

      Definition outMuSAlgi{S : kMo} {C : kMo} {X : kMo -> kMo}
                 (v : MuSAlgi S C X) : (F MuSAlgi) S C X :=
        match v with
        | muSAlg A r S1 C1 X1 d => salgMap r S1 C1 X1 d
        end.
      
    End MuSAlg.

    Section MuAlg.

      Variable F : KAlgi -> KAlgi.
      Variable algMap : forall {A B : KAlgi}, CastAlgi A B -> CastAlgi (F A) (F B).

      Inductive MuAlgi : KAlgi := 
        muAlg : forall A : KAlgi,
          (forall (C : kMo) (X : kMo -> kMo), A C X -> MuAlgi C X) ->
          (forall (C : kMo) (X : kMo -> kMo), F A C X -> MuAlgi C X).

      Definition inMuAlgi{C : kMo} {X : kMo -> kMo} (d: (F MuAlgi) C X) : MuAlgi C X :=
        muAlg MuAlgi (fun C X d => d) C X d.

      Definition outMuAlgi{C : kMo} {X : kMo -> kMo}
                 (v : MuAlgi C X) : (F MuAlgi) C X :=
        match v with
        | muAlg A r C1 X1 d => algMap r C1 X1 d
        end.
      
    End MuAlg.
End Defs.
