(* try applying Bove-Capretta method from 
   http://www.duplavis.com/venanzio/publications/General_Recursion_MSCS_2005.pdf *)
Require Import Program Coq.Lists.List Psatz.

Local Open Scope list_scope.

Section WordsByP.

  Variable A : Set.

  Section Span.
    Variable p : A -> bool.

    Fixpoint span (l:list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | x::xs => if p x then let (ys, zs) := span xs in (x::ys, zs) else (nil, l)
      end.

  End Span.

  Variable p : A -> bool.

  Definition break := span (fun a => negb (p a)).

  Inductive Path : list A -> Set :=
    NilP : Path nil
  | ConsP : forall(hd:A)(tl:list A), Path tl -> Path (snd (break tl)) -> Path (hd :: tl).

  Fixpoint pathBreak(l : list A)(u : Path l) : Path (snd (break l)).
    inversion u.    
    - apply NilP.
    - simpl.
      destruct (p hd) eqn:e; simpl.
        -- apply ConsP.      
           --- exact H.
           --- exact H0.
        -- destruct (break tl) eqn:e'.
           simpl.
           set (i := pathBreak tl H).
           rewrite e' in i.
           exact i.
  Defined.

  Theorem listPath : forall(l : list A), Path l.
    induction l.
    - apply NilP.
    - apply ConsP.
      -- apply IHl.
      -- apply pathBreak.
         exact IHl.
  Defined.

  Fixpoint wordsByPh (l:list A)(u : Path l) : list (list A) :=
    match u with
    | NilP => nil
    | ConsP hd tl u1 u2 =>
        if p hd then
          wordsByPh tl u1
        else
          let b := break tl in
            (hd::fst b)::(wordsByPh (snd b) u2)
    end.

  Definition wordsByP(l : list A) : list (list A) :=
    wordsByPh l (listPath l).

End WordsByP.

Arguments wordsByP {A}.

Section test.

Eval compute in (wordsByP (Nat.eqb 0) (0 :: 1 :: 1 :: 2 :: 0 :: 1 :: 3 :: 5 :: 0 :: nil)).

End test.
