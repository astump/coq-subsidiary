Require Import Coq.Lists.List.

Definition FmapT(A B : Set)(F : Set -> Set) : Set := forall(f : A -> B), F A -> F B.

Class Functor (F : Set -> Set) :=
  {
  fmap : forall {A B : Set}, FmapT A B F;
  }.


Definition Id(X:Set) : Set := X.
Global Instance FunId : Functor Id := { fmap := fun A B c xs => c xs }.

Global Instance FunOption : Functor option :=
  { fmap := fun A B c o => match o with Some x => Some (c x) | None => None end}.

Global Instance FunList : Functor list :=
  { fmap := fun A B c o => map c o }.

Definition Const(T: Set) : Set -> Set := fun _ => T.
Global Instance FunConst(T : Set)  : Functor (Const T) :=
  {fmap := fun A B f xs => xs}.

Definition FmapId(F : Set -> Set)(FunF : Functor F) : Set :=
  forall (A : Set) (x : F A), fmap (fun x => x) x = x .
