Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Functors.
Require Import Mu.

From Coq Require Import List.
(* This is our library for generating definitions via Ltac: *)
(* From idt Require Import all. *)
From Coq Require Import Nat.

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

  Fixpoint listFold(l : list A){X : Set}(alg : ListF X -> X) : X :=
  match l with
    nil => alg Nil
  | cons hd tl => alg (Cons hd (listFold tl alg))
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

  Definition List := Subrec ListF .

  (* -------------------------------------------------------------------------------- *)
  (* Smart constructors for List as Initial Carrier. *)
  (* -------------------------------------------------------------------------------- *)

  Definition inList : ListF List -> List := inn ListF.
  Definition outList : List -> ListF List := out ListF (fold ListF).
  Definition mkNil : List := inList Nil.
  Definition mkCons (hd : A) (tl : List) : List := inList (Cons hd tl).

  (* -------------------------------------------------------------------------------- *)
  (* despite noncanonicity, some expected properties of constructors hold             *)
  (* -------------------------------------------------------------------------------- *)

  Lemma nilCons : forall(h:A)(t:List), mkNil = mkCons h t -> False.
    intros h t u.
    assert (c : outList mkNil = outList (mkCons h t)).
    + rewrite u; reflexivity.
    + discriminate c.
  Qed.

  Lemma consCons : forall(h1 h2 : A)(t1 t2 : List),
                   mkCons h1 t1 = mkCons h2 t2 ->
                   h1 = h2 /\ t1 = t2.
    intros h1 h2 t1 t2 u.
    assert (c : outList (mkCons h1 t1) = outList (mkCons h2 t2)).
    + rewrite u; reflexivity.
    + simpl in c.
      injection c.
      auto.
    Qed.

  (* -------------------------------------------------------------------------------- *)
  (* (list A) => List A injection                                                     *)
  (* -------------------------------------------------------------------------------- *)

  Definition toList (xs : list A) : List := listFold xs (inn ListF).
  Definition fromList : List -> list A :=
    fold ListF (Const (list A)) (FunConst (list A))
         (rollAlg (fun R fo rec fr => listIn (fmap rec fr))) .
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
    - change (fromList (toList (a :: xs))) with (cons a (fromList (toList xs))).
      rewrite IHxs.
      reflexivity.
  Qed.

  (* -------------------------------------------------------------------------------- *)
  (* Some basic list operations *)
  (* -------------------------------------------------------------------------------- *)

  Definition LengthAlg(C : Set) : Alg ListF (Const nat) :=
   rollAlg
   (fun _ _ rec xs =>
       match xs with
         Nil => 0
       | Cons hd tl => 1 + rec tl
       end).

  Definition length : List -> nat :=
    fold ListF (Const nat) (FunConst nat) (LengthAlg List).

  Definition appendAlg : Alg ListF (Const (List -> List)) :=
    rollAlg (fun _ _ rec xs ys =>
               match xs with
               | Nil => ys
               | Cons hd tl => mkCons hd (rec tl ys)
               end
            ).
  Definition append (xs ys : List) : List :=
    fold ListF _ _ appendAlg xs ys.

  Definition getNilAlg(R : Set) : Alg ListF option :=
    rollAlg (fun _ _ rec xs =>
               match xs with
                 Nil => None
               | Cons hd tl =>
                 match (rec tl) with
                   None => Some tl
                 | Some tl => Some tl
                 end
               end).

  Definition getNilh(xs : List) : option List :=
    fold ListF option FunOption (getNilAlg List) xs.

  Definition getNil(xs:List) : List :=
    match getNilh xs with
      None => xs
    | Some q => q
    end.



  (* -------------------------------------------------------------------------------- *)
  (* Dependent stuff *)
  (* -------------------------------------------------------------------------------- *)

  Definition lkMo := List -> Prop.
  Inductive ListFi(R : lkMo) : lkMo :=
    nilFi : ListFi R mkNil
  | consFi : forall (h : A)(t : List), R t -> ListFi R (mkCons h t).

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
  Definition toListi(xs : list A) : Listi (toList xs) := listFoldi xs Listi inni.
  Definition listAlgi := Algi ListF ListFi.

  Definition ListFoldTi(R : List -> Prop)(d : List) : Prop :=
    FoldTi ListF (Algi ListF ListFi) R d.

End List.

Arguments Nil {A} {X}.
Arguments Cons {A} {X} a r.

Arguments mkNil{A}.
Arguments mkCons{A}.
Arguments inList {A}.
Arguments toList {A} xs.
Arguments fromList {A} xs.
Arguments canonList {A} xs.
Arguments inj{A} xs.
Arguments getNil{A}.
Arguments getNilh{A}.
Arguments ListFi {A} R xs.

Arguments ListFoldTi{A}.

Definition ex  : list nat := [1 ; 2 ; 3 ; 4 ; 5 ; 6].
Definition ex' : List nat := (toList ex).

Ltac fromCons := change (fromList (mkCons ?h ?t)) with (h :: fromList t).

(* prove P (toList xs) using Subreci for lists *)
Ltac listInd P xs :=
  let ind := fresh "ind" in
    set (ind := foldi (Fi := ListFi) (toList xs) P);
    simpl in ind; try (rewrite (inj xs) in ind);
    apply ind; clear ind; [apply FunConsti | apply rollAlgi; intros R fo ih d fd; destruct fd; [ idtac | fromCons] | exact (toListi _ xs)].

Arguments nilCons{A}{h}{t} e.
Arguments consCons{A}{h1}{h2}{t1}{t2} e.
Arguments listFold{A} l {X} alg.
