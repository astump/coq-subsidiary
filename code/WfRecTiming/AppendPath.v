Require Import Coq.Lists.List.
Local Open Scope list_scope.

Section AppendPath.

  Variable A : Set.

  Inductive Path : list A -> Set :=
    Empty : Path nil
  | Descend : forall(hd : A)(tl : list A), Path tl -> Path (hd :: tl).

  Fixpoint appendP(l1 l2:list A)(u : Path l1) : list A :=
    match u with
    | Empty => l2
    | Descend hd tl u' =>
        hd :: (appendP tl l2 u')
    end.

End AppendPath.

Arguments appendP{A}.

