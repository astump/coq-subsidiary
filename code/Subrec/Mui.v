Require Import Kinds.

(* -------------------------------------------------------------------------------- *)
(* Mu over propositions. *)
(* -------------------------------------------------------------------------------- *)
Section Defs.
    Variable I : Set.
    Definition kMo := I -> Prop.
    Definition KAlgi := (kMo -> kMo) -> Set.

    Definition CastAlgi(alg1 alg2 : KAlgi) := 
      forall (X : kMo -> kMo), alg1 X -> alg2 X.

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

    Section MuAlg.

      Variable F : KAlgi -> KAlgi.
      Variable algMap : forall {A B : KAlgi}, CastAlgi A B -> CastAlgi (F A) (F B).

      Inductive MuAlgi : KAlgi := 
        muAlg : forall A : KAlgi,
          (forall (X : kMo -> kMo), A X -> MuAlgi X) ->
          (forall (X : kMo -> kMo), F A X -> MuAlgi X).

      Definition inMuAlgi {X : kMo -> kMo} (d: (F MuAlgi) X) : MuAlgi X :=
        muAlg MuAlgi (fun X d => d) X d.

      Definition outMuAlgi {X : kMo -> kMo}
                 (v : MuAlgi X) : (F MuAlgi) X :=
        match v with
        | muAlg A r X1 d => algMap r X1 d
        end.
      
    End MuAlg.
End Defs.
