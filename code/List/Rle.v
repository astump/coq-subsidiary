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

Require Import List.ExtraLib.
Require Import List.Repeat.
Require Import Rld.

Require Import Span.
Require Import SpanPfs.Append.
Require Import SpanPfs.Forall.
Require Import SpanPfs.GuardPres.

Import ListNotations.


Section RLE.

  Variable A : Set.
  Variable eqb : A -> A -> bool.
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
    set (ind := foldi (Fi := ListFi A) (toList xs)
                  (fun X xs => rld (rle xs) = fromList xs)
        ).
    simpl in ind; rewrite (inj A xs) in ind.
    apply ind. apply FunConsti.
    apply rollAlgi; unfold AlgF.
    intros R _ fo _ ih d fd.
    destruct fd.
    - reflexivity.
    - change (fromList (consInit A h t)) with (h :: fromList t). 
      simpl'.
      change (fold (ListF A) RleCarr (FunConst (list (nat * A))) RleAlg) with rle.
      destruct (spanr A (Subrec.Subrec (ListF A)) (fold (ListF A)) (eqb h) t) as (l,r) eqn:e.
      set (sg := guardPres A R fo (eqb h) t H l r e).
      rewrite (append A R fo (eqb h) t H l r e).
      set (sf := spanForall A R fo (eqb h) t H l r e).
      set (uu := Foralleqb eqb eq h l sf).
      destruct r.
      -- simpl'.
         rewrite <- uu.
         reflexivity.
      -- inversion sg.
      --- contradiction (nilCons A a s H0).
      --- destruct (consCons A h0 a t0 s H1) as (_, q); clear H1.
          rewrite q in H0; clear q.
          change (fromList (inList (Cons a s))) with (a :: fromList s).
          simpl'.
          rewrite (rldTackOn a (rle s)).
          rewrite (ih s H0).
          rewrite <- uu.
          reflexivity.
    - exact (toListi _ xs).
    Qed.

End RLE.

(* testcases *)

Definition test := rle nat eqb (toList (1 :: 1 :: 1 :: 2 :: 2 :: 3 :: 3 :: 3 :: 3 :: 4 :: 5 :: 5 :: [])).

Eval compute in test.


