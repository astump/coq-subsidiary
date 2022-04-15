Require Import Lists.List.

Print well_founded.

Section SmallerListWf.
  Variable A : Type.

Inductive smallerList : list A -> list A -> Prop :=
| sl_nil : forall(h:A)(t:list A) , smallerList nil (cons h t)
| sl_cons : forall (h h':A)(x y : list A) , smallerList x y -> smallerList (cons h x) (cons h' y).

(*
Inductive nt : Prop :=
  ntZ : nt
| ntS : nt -> nt.

Definition slSize : forall(l1 l2 : list A), smallerList l1 l2 -> nt.
  intros l1 l2 p.
  induction p.
  - exact ntZ.
  - exact (ntS IHp).
Defined.
*)

Lemma accSlNil : Acc smallerList nil.
apply Acc_intro.
intros y uy.
inversion uy.
Defined.

Lemma triple : forall(x y : list A),
    smallerList x y ->
    forall (z : list A),
    smallerList y z ->
      exists h z', z = h :: z' /\ smallerList x z'.
intros x y p1.
induction p1; intros z p2.
- inversion p2.
  exists h'.
  exists y.
  apply conj.
  -- trivial.
  -- inversion H2; apply sl_nil.
- inversion p2.
  set (ih := IHp1 y0 H2).
  destruct ih.
  destruct H3.  
  destruct H3.
  exists h'0. exists y0.
  apply conj.
  trivial.
  rewrite H3.
  apply sl_cons.
  assumption.
Defined.
  
Lemma dec : forall (y x : list A), smallerList x y -> Acc smallerList x.
  induction y; intros x s.
  - inversion s.
  - inversion s.
    -- exact accSlNil.
    -- apply Acc_intro.
       intros y1 sy1.       
       apply IHy.
       set (c := sl_cons h h x0 y H1).
       set (u := triple y1 (h :: x0) sy1 (h :: y) c).
       destruct u.
       destruct H3.
       destruct H3.
       inversion H3.                    
       assumption.
Defined.

Theorem smallerListWf : well_founded smallerList.
  unfold well_founded.
  intro a.
  apply Acc_intro.
  exact (dec a).
Defined.

Theorem smallerListTail : forall (t : list A)(h : A), smallerList t (h :: t).
  induction t; intro h.
  - apply sl_nil.
  - apply sl_cons.
    apply IHt.
Defined.
 
Theorem smallerListSwap :
  forall (h h' : A)(t t' : list A), smallerList t (h :: h' :: t') -> smallerList t (h' :: h :: t').
  intros h h' t t' p.
  inversion p as [|x y z q u].
  - apply sl_nil.
  - inversion u as [|x' y' z' q' u'].
    -- apply sl_cons; apply sl_nil.
    -- apply sl_cons; apply sl_cons.
       exact u'.
Defined.

Theorem smallerListCons :
  forall (t' t: list A)(h : A), smallerList t t' -> smallerList t (h :: t').
  intros t'.
  induction t'; intros t h p.
  - inversion p.
  - inversion p as [|x y z q u].
    -- apply sl_nil.
    -- apply sl_cons.
       apply IHt'.
       assumption.
Defined.
    
End SmallerListWf.

(*
Arguments slSize{A}{l1}{l2}.

Eval compute in (slSize (smallerListTail nat (repeat 1 10000) 2)).

*)