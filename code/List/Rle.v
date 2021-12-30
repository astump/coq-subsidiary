Require Import Subrec.
Require Import Subreci.
Require Import Kinds.
Require Import Mu.
Require Import List.
Require Import Functors.

Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Plus.
Require Import Le.

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Span.

Import ListNotations.


Section RLE.

  Variable A : Set.
  (* Bool equality *)
  Variable eqb : A -> A -> bool.
  (* propositional equality *)
  Variable eq : forall a1 a2, eqb a1 a2 = true -> a1 = a2.
    
  (* -------------------------------------------------------------------------------- *)
  (* Run-Length encode *)
  (* -------------------------------------------------------------------------------- *)

  Definition tackOn(prev : A)(xs : list (nat * A)) : list (nat * A) :=
    match xs with
      [] => [(1,prev)]
    | (count,x) :: xs' =>
      if eqb prev x then
        (succ count,x) :: xs'
      else
        (1,prev) :: xs
    end.

  Definition RleCarr := Const (list (nat * A)).
  Definition RleAlg : Alg (ListF A) (List A) RleCarr :=
    rollAlg (ListF A)
            (fun R reveal fo out eval xs =>
          match xs with
          | Nil => []
          | Cons hd tl =>
            let (p,s) := spanr A R fo (eqb hd) tl in
            let e := (succ (length p), hd) in
                match s with
                  Nil          => [e]
                | Cons hd' tl' => e :: tackOn hd' (eval tl')
                end
          end).

  Definition rle(xs : List A) : list (nat * A)
    := @fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg xs.

  (* -------------------------------------------------------------------------------- *)
  (* Run-Length decode *)
  (* -------------------------------------------------------------------------------- *)
    
  Fixpoint repeat(count : nat) (v : A) : list A :=
    match count with
    | 0   => []
    | S n =>  v :: (repeat n v)
    end.

  Fixpoint rld(xs : list (nat * A)) : list A :=
    match xs with
    | [] => []
    | (n, v) :: tl => repeat n v ++ rld tl
    end.


(*
  (* -------------------------------------------------------------------------------- *)
  (* Helper tactics *)  
  (* -------------------------------------------------------------------------------- *)
  Ltac foldCollect :=
    change (fold (ListF A) CollectF FunCollectF (CollectAlg ?x ?T) ?tl ?n)
    with
      (collect x tl n).

  Ltac foldRle :=
    change (fold ?F ?Carr ?FuNCarr RleAlg ?xs) with (rle xs).
  
  (* -------------------------------------------------------------------------------- *)
  (* Theorems (rle) *)  
  (* -------------------------------------------------------------------------------- *)

  Definition foi := foi (Fi := (ListFi A)).
  
  Definition repeatCollectP (S : kMo (ListF A))(xs : List A) : Prop :=
    forall (x : A)
           (k n : nat)
           (l : ListF A (List A)),
      let p := collect x xs k in
      p = (n, l) ->
      repeat n x ++ (fromList (inL l)) = repeat k x ++ fromList xs
      /\ ListFi A S (inL l).

  Lemma hopRepeat : forall (n : nat)(a : A)(xs : list A),
      a :: repeat n a ++ xs = repeat n a ++ a :: xs.
    intros. induction n; simpl.
    - reflexivity.
    - rewrite IHn. reflexivity.
  Qed.

  Lemma repeatCollect
        (S : kMo (ListF A))
        (fo : forall d : List A, FoldTi (ListF A) (Algi (ListF A) (ListFi A)) S d)
        (out : forall d : Init (ListF A), S d -> ListFi A S d)
    : forall (xs : List A)
             (Rxs : S xs),
        repeatCollectP S xs.
    intros xs Sxs x k n l.
    apply (fo xs
               (fun X xs => repeatCollectP S xs)).
    + apply constimap.
    + apply rollAlgi. unfold AlgF.
    intros R reveal _ _ _ ih d fd.
    destruct fd as [| hd tl Rtl].
    - unfold repeatCollectP ; intros.
      simpl in H.
      inversion H.
      apply conj.
      -- reflexivity.
      -- apply nilFi.
    - unfold repeatCollectP.
      intros x0 k0 n0 l0.
      simpl'; destruct (eqb hd x0) eqn:u1.
      -- foldCollect.
         intro u2.
         assert (ihtl := ih tl Rtl); clear ih.
         unfold repeatCollectP in ihtl.      
         destruct (collect x0 tl (succ k0)) eqn:e1.
         destruct l1; inversion u2 as [(q0,q1)]; clear u2 q1.
         --- assert (ihtl2 := ihtl x0 (succ k0) n1 Nil e1); clear ihtl.
             destruct ihtl2 as [ihtl2a ihtl2b].
             rewrite q0 in ihtl2a.
             change (fromList (inL Nil)) with (nil (A:=A)) in ihtl2a. 
             change (listIn A Nil) with (nil (A:=A)).   
             rewrite ihtl2a.
             simpl.
             change (toT (ListF A) tl) with (fromList tl).
             rewrite (eq hd x0 u1).
             apply conj.
             ---- apply hopRepeat.
             ---- assumption.
         --- rewrite q0 in e1; clear q0.
             rewrite (eq hd x0 u1); clear u1.
             assert (ihtl2 := ihtl x0 (succ k0) n0 (Cons a i) e1); clear ihtl.
             change (listIn A (Cons a (toT (ListF A) i))) with (fromList (inL (Cons a i))).
             destruct ihtl2 as [ihtl2a ihtl2b].
             rewrite ihtl2a.
             simpl.
             apply conj.
             ---- apply hopRepeat.             
             ---- apply ihtl2b.
      -- intro u2; inversion u2 as [(q0,q1)]; clear u2 q0 q1.
         clear u1.
         apply conj.
         --- reflexivity.
         --- apply consFi.
             apply reveal.
             assumption.
    + exact Sxs.
  Qed.

  Lemma rldTackOn(a : A)(xs : list (nat * A)) :
                 rld (tackOn a xs) = a :: rld xs.
  case xs as [|h t]; simpl.
  + reflexivity.
  + destruct h as [n a'].
    destruct (eqb a a') eqn:e.    
    - rewrite (eq a a' e).
      reflexivity.
    - reflexivity.
  Qed.

  Theorem RldRle : forall (xs : list A), rld (rle (toList xs)) = xs.
    intros xs.
    set (ind := foi (toList xs)
                    (fun X xs => rld (rle xs) = fromList xs)
        ).
    simpl in ind; rewrite (inj A xs) in ind.
    apply ind. apply constimap.
    apply rollAlgi; unfold AlgF.
    intros R rev fo sfo out ih d H.
    destruct H.
    - reflexivity.
    - fold (List A) in *.
      simpl'.
      change (toT (ListF A) t) with (fromList t).
      foldCollect.
      foldRle.
      destruct (collect h t 1) eqn:co.
      Check repeatCollect.
      set (rc := repeatCollect R fo out t H h 1 n l co).
      destruct rc as [rc1 rc2].
      destruct l as [| a l].
      + assumption.
      + change (fromList (inL (Cons a l))) with (a :: fromList l) in rc1.
        change (listIn A (Cons h (fromList t))) with (h :: fromList t).
        change (repeat 1 h ++ fromList t) with (h :: fromList t) in rc1.
        rewrite <- rc1.
        change (rld ((n,h) :: tackOn a (rle l))) with (repeat n h ++ rld (tackOn a (rle l))).
        rewrite (rldTackOn a (rle l)).
        rewrite (ih l).
        * reflexivity.
        * inversion rc2.
          ** contradiction (nilCons A a l H0).
          ** destruct (consCons A h0 a t0 l H1) as [_ e].
             rewrite e in H0.
             assumption.
    - exact (toListi _ xs).
    Qed.
*)

End RLE.

(* testcases *)

Definition test := rle nat eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


