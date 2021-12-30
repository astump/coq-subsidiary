Class Functor (F : Set -> Set) :=
  {
  fmap : forall {A B : Set}(f : A -> B), F A -> F B;
  }.


Definition Id(X:Set) : Set := X.
Global Instance FunId : Functor Id := { fmap := fun A B c xs => c xs }.

Global Instance FunOption : Functor option :=
  { fmap := fun A B c o => match o with Some x => Some (c x) | None => None end}.

Definition Const(T: Set) : Set -> Set := fun _ => T.
Global Instance FunConst(T : Set)  : Functor (Const T) :=
  {fmap := fun A B f xs => xs}.

