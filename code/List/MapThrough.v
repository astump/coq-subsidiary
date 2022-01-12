(* similar to repeatedly from Haskell's Data.List.Extra, as an Alg *)

Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import List.List.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Definition mappedT(A B : Set) : Set :=
  forall(R : Set)(fo:FoldT (Alg (ListF A)) R),
    A -> R -> B * R.

Section MapThrough.

  Context {A : Set}.

  Definition MapThroughAlg
             {B : Set}
             (m:mappedT A B)
             (C : Set) : Alg (ListF A) C (Const (List B)) :=
    rollAlg 
      (fun R reveal fo eval xs => 
         match xs with
           Nil => mkNil 
         | Cons hd tl =>
           let (b,c) := m R fo hd tl in
             mkCons b (eval c)
         end).

  Definition mapThroughr{R : Set}(fo:FoldT (Alg (ListF A)) R)
                        {B : Set}(m:mappedT A B)
                   : R -> List B :=
    fo (Const (List B)) (FunConst (List B)) (MapThroughAlg m R).

  Definition mapThrough{B : Set}(m:mappedT A B)
                   : List A -> List B :=
    mapThroughr (fold (ListF A)) m.

(*
  Definition mapThroughIndT(B : Set)(m:mappedT A B)
          (P : List A -> List B -> Prop)(xs : List A): Prop :=
          P mkNil mkNil ->
          (forall(a : A)(b:B)(xs xs' : List A)(ys : List B)
                 (R : List A -> Prop)
                 (fo : forall d : List A , FoldTi (ListF A) (Algi (ListF A) ListFi) R d),
              R xs ->
              m (List A) (fold (ListF A)) a xs = (b,xs') ->
              P xs' ys ->
              P (mkCons a xs) (mkCons b ys)) ->
          P xs (mapThrough m xs).

  Theorem mapThroughInd(B : Set)(m:mappedT A B)
          (P : List A -> List B -> Prop)(xs : List A): mapThroughIndT B m P xs.
  Admitted.          
*)
End MapThrough.

