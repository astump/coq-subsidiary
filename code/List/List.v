
Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import Mu.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.

Import ListNotations.

Section List.
  Variable A : Set. 

  (* -------------------------------------------------------------------------------- *)
  (* List Functor *)
  (* -------------------------------------------------------------------------------- *)

  Inductive ListF(X : Set) : Set :=
  | Nil : ListF X
  | Cons : A -> X -> ListF X.

  Arguments Nil {X}.
  Arguments Cons {X} a r.

  Global Instance FunListF : Functor ListF :=
    {fmap :=
       fun R1 R2 f xs
       => match xs with
         | Nil => Nil
         | Cons hd tl => Cons hd (f tl)
         end
    }.

  Definition listFmapId{A0 : Set} : forall (d : ListF A0), fmap id d = d .
    intros.
    destruct d.
    - reflexivity.
    - simpl. unfold id. reflexivity.
  Defined.

  (* -------------------------------------------------------------------------------- *)
  (* Building IndInj typeclass for ListF. *)
  (* -------------------------------------------------------------------------------- *)

  Fixpoint listFold(l : list A)(X : Set)(alg : ListF X -> X) : X :=
  match l with
    nil => alg Nil
  | cons hd tl => alg (Cons hd (listFold tl X alg))
  end.

  Definition listIn(d : ListF (list A)) : list A :=
    match d with
      Nil => []
    | Cons hd tl => hd :: tl
    end.

  Definition listOut : list A -> ListF (list A) :=
    fun l =>
      match l with
      | [] => Nil
      | (hd :: tl) => Cons hd tl
      end.
  
  Definition List := @Subrec ListF .

  Definition ListOut : List -> ListF List := @out ListF FunListF .

  (* -------------------------------------------------------------------------------- *)
  (* Smart constructors for List as Initial Carrier. *)
  (* -------------------------------------------------------------------------------- *)

  Definition inL : ListF List -> List := inn ListF.
  Definition prenil : forall (R S : Set), (ListF R -> S) -> S :=
    fun R S f => f Nil.
  
  Definition nilInit : List := prenil List List inL.
  
  Definition precons : forall (R S : Set), A -> R -> (ListF R -> S) -> S :=
    fun R S hd tl f => f (Cons hd tl).

  Definition consInit (hd : A) (tl : List) : List :=
    precons List List hd tl inL.

  (* -------------------------------------------------------------------------------- *)
  (* despite noncanonicity, some expected properties of constructors hold             *)
  (* -------------------------------------------------------------------------------- *)

  Lemma nilCons : forall(h:A)(t:List), nilInit = consInit h t -> False.
    intros h t u.
    assert (c : ListOut nilInit = ListOut (consInit h t)).
    + rewrite u; reflexivity.    
    + discriminate c.    
  Qed.

  Lemma consCons : forall(h1 h2 : A)(t1 t2 : List),
                   consInit h1 t1 = consInit h2 t2 ->
                   h1 = h2 /\ t1 = t2.
    intros h1 h2 t1 t2 u.
    assert (c : ListOut (consInit h1 t1) = ListOut (consInit h2 t2)).
    + rewrite u; reflexivity.
    + simpl in c.
      injection c.
      auto.
    Qed.

  (* -------------------------------------------------------------------------------- *)
  (* (list A) => List A injection                                                     *)
  (* -------------------------------------------------------------------------------- *)

  Definition toList (xs : list A) : List := listFold xs List (inn ListF).
  Definition fromList : List -> list A :=
    fold ListF (Const (list A)) (FunConst (list A))
         (rollAlg ListF (fun R reveal fo out eval fr => listIn (fmap eval fr))) .
  Definition canonList (xs : List) : List := toList (fromList xs).

  Definition ListPT :
    forall (P : list A -> Prop),
      (List -> Prop) :=
    fun P xs => P (fromList xs).

  Definition liftL :
    forall (P : list A -> Prop)
      (Pxs : forall xs, P xs),
      (forall xs, ListPT P xs).
    intros.
    unfold ListPT.
    apply Pxs.
  Defined.

  Theorem inj : forall (xs : list A), fromList (toList xs) = xs.
    induction xs.
    - simpl. auto.
    - replace (fromList (toList (a :: xs))) with (cons a (fromList (toList xs))).
      rewrite IHxs.
      reflexivity.
      auto.
  Qed.
        
  Definition ForaL(P : A -> Prop)(l : List) : Prop := Forall P (fromList l).

  (* -------------------------------------------------------------------------------- *)
  (* Some basic list operations *)
  (* -------------------------------------------------------------------------------- *)

  (* this used to be an Alg, but I need an SAlg other places -- Aaron *)
  Definition LengthAlg(C : Set) : Alg ListF C (Const nat) :=
   rollAlg ListF
   (fun _ _ _ _ eval xs =>
       match xs with
         Nil => 0
       | Cons hd tl => 1 + eval tl
       end).

  Definition length : List -> nat :=
    fold ListF (Const nat) (FunConst nat) (LengthAlg List).

  Definition appendAlg : Alg ListF List (Const (List -> List)) :=
    rollAlg _
            (fun _ _ _ _ eval xs ys =>
               match xs with
               | Nil => ys
               | Cons hd tl => consInit hd (eval tl ys)
               end
            ).
  Definition append (xs ys : List) : List :=
    fold ListF _ _ appendAlg xs ys.
  

  (* -------------------------------------------------------------------------------- *)
  (* Dependent stuff *)
  (* -------------------------------------------------------------------------------- *)
      
  Definition lkMo := List -> Prop.
  Inductive ListFi(R : lkMo) : lkMo :=
    nilFi : ListFi R nilInit
  | consFi : forall (h : A)(t : List), R t -> ListFi R (consInit h t).

  Arguments nilFi {R}.
  Arguments consFi {R} h t rt.

  Definition ListFiMap(B C : lkMo)
             (f : forall l : List , B l -> C l)
             (l : List)(d : ListFi B l) : ListFi C l :=
    match d with
      nilFi => nilFi
    | consFi hd tl rtl => consFi hd tl (f tl rtl)
    end.

  Fixpoint listFoldi
           (l : list A)
           (X : lkMo)
           (alg : forall l : List , ListFi X l -> X l)
           { struct l} :
    X (toList l) :=

    match l with
      [] => alg (toList []) nilFi
    | hd :: tl =>
      alg (toList (cons hd tl))
          (consFi
             hd
             (toList tl)
             (listFoldi tl X alg))
    end.


    (* we bundle all of the boilerplate into DepF *)
  Global Instance depList : DepF ListF (ListFi) :=
    {
    FiMap := ListFiMap;
    }.

  Definition Listi := Subreci ListF ListFi.
  Definition toListi(xs : list A) : Listi (toList xs) := listFoldi xs Listi (inni depList).
  Definition listAlgi := Algi ListF ListFi.

End List.

Arguments Nil {A} {X}.
Arguments Cons {A} {X} a r.

Arguments inL {A}.
Arguments toList {A} xs.
Arguments fromList {A} xs.
Arguments canonList {A} xs.

Arguments ForaL {A} P l.

Definition ex  : list nat := [1 ; 2 ; 3 ; 4 ; 5 ; 6].
Definition ex' : List nat := (toList ex).

