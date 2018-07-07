Require Import syntax.
Require Import substitution.
Require Import statics.
From stdpp Require Import gmap.
From stdpp Require Import set.

(* Unit *)
Definition x := 0.

Definition UnitType t := All t (Arr (Typ t) (Typ t)).
Definition Unit t := Lam2 t (Lam x (Typ t) (Var x)).

Lemma UnitTypeChecks th g t : WellTyped th g (Unit t) (UnitType t).
Proof. constructor. constructor. repeat constructor. Qed.

(* Pairs *)
Definition f := 0.
Definition x1 := 1.
Definition x2 := 2.

Definition PairType r t1 t2 := All r (Arr (Arr t1 (Arr t2 (Typ r))) (Typ r)).
Definition Pair r e1 t1 e2 t2 := Lam2 r (Lam f (Arr t1 (Arr t2 (Typ r))) (App (App (Var f) e1) e2)).
Definition PairLeft e t1 t2 := App (App2 e t1) (Lam x1 t1 (Lam x2 t2 (Var x1))).
Definition PairRight e t1 t2 := App (App2 e t2) (Lam x1 t1 (Lam x2 t2 (Var x2))).

Lemma PairTypeChecks th g r t1 t2 e1 e2 : (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) -> WellTyped th g (Pair r e1 t1 e2 t2) (PairType r t1 t2).
Proof. intros He1 He2. repeat constructor. apply AppT with t2. apply AppT with t1. apply VarT. apply He1. apply He2. Qed.

Example UnitPairTypeExample th g r t f : WellTyped th g (Pair r (Unit t) (UnitType t) (Unit f) (UnitType f)) (PairType r (UnitType t) (UnitType f)).
Proof. apply PairTypeChecks; intros; apply UnitTypeChecks. Qed.

Lemma PairLeftChecks th g r e1 e2 t1 t2 : 
  WellTTyped th t1 ->
  not (set_elem_of r (FVT t1)) -> not (set_elem_of r (FVT t2)) ->
  (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) ->
  WellTyped th g (Pair r e1 t1 e2 t2) (PairType r t1 t2) -> 
  WellTyped th g (PairLeft (Pair r e1 t1 e2 t2) t1 t2) t1.
Proof.
  intros Hth Ht1 Ht2 He1 He2 HPair.
  apply AppT with (Arr (t1) (Arr t2 (t1))). 
  assert ((Arr (Arr (t1) (Arr t2 t1)) t1) = subst_t_t (Arr (Arr (t1) (Arr t2 (Typ r))) (Typ r)) t1 r).
  { simpl. destruct (var_dec r r); try contradiction. rewrite none_subst_t. rewrite none_subst_t. reflexivity. assumption. assumption. } 
  rewrite H. apply App2T.
  - apply HPair. 
  - apply Hth. 
  - constructor. constructor. rewrite insert_commute. apply VarT. inversion 1.
Qed.

Lemma PairRightChecks th g r e1 e2 t1 t2 : 
  WellTTyped th t2 ->
  not (set_elem_of r (FVT t1)) -> not (set_elem_of r (FVT t2)) ->
  (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) ->
  WellTyped th g (Pair r e1 t1 e2 t2) (PairType r t1 t2) -> 
  WellTyped th g (PairRight (Pair r e1 t1 e2 t2) t1 t2) t2.
Proof.
  intros Hth Ht1 Ht2 He1 He2 HPair.
  apply AppT with (Arr (t1) (Arr t2 (t2))).
  assert ((Arr (Arr (t1) (Arr t2 t2)) t2) = subst_t_t (Arr (Arr (t1) (Arr t2 (Typ r))) (Typ r)) t2 r).
  { simpl. destruct (var_dec r r); try contradiction. rewrite none_subst_t. rewrite none_subst_t. reflexivity. assumption. assumption. } 
  rewrite H. apply App2T.
  - apply HPair. 
  - apply Hth. 
  - constructor. constructor. apply VarT.
Qed.

(* Binary Sums *)
Definition f1 := 0.
Definition f2 := 1. 

Definition SumType r t1 t2 := All r (Arr (Arr t1 (Typ r)) (Arr (Arr t2 (Typ r)) (Typ r))).
Definition SumLeft r t1 t2 e1 := Lam2 r (Lam f1 (Arr t1 (Typ r)) (Lam f2 (Arr t2 (Typ r)) (App (Var f1) (e1)))).
Definition SumRight r t1 t2 e2 := Lam2 r (Lam f1 (Arr t1 (Typ r)) (Lam f2 (Arr t2 (Typ r)) (App (Var f2) (e2)))).

Lemma SumLeftTypeChecks th g t1 t2 r e1 : (forall th g, WellTyped th g e1 t1) -> WellTyped th g (SumLeft r t1 t2 e1) ((SumType r t1 t2)).
Proof. intros He1. repeat constructor. apply AppT with t1. rewrite insert_commute. apply VarT. inversion 1. apply He1. Qed.

Lemma SumRightTypeChecks th g t1 t2 r e2 : (forall th g, WellTyped th g e2 t2) -> WellTyped th g (SumRight r t1 t2 e2) ((SumType r t1 t2)).
Proof. intros He2. repeat constructor. apply AppT with t2. apply VarT. apply He2. Qed.

(* Natural Numbers *)
Definition s := 0.
Definition z := 1.

Definition NatType r := All r (Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))).
Definition Z r := Lam2 r (Lam z (Typ r) (Lam s (Arr (Typ r) (Typ r)) (Var z))).
Definition Succ r e := Lam2 r (Lam z (Typ r) (Lam s (Arr (Typ r) (Typ r)) (App (Var s) (App (App (App2 e (Typ r)) (Var z)) (Var s))))).

Lemma ZChecks th g r : WellTyped th g (Z r) (NatType r).
Proof. repeat constructor. rewrite insert_commute. apply VarT. inversion 1. Qed.

Lemma SuccChecks th g r e : (forall th g, WellTyped th g e (NatType r)) -> WellTyped th g (Succ r e) (NatType r).
Proof. 
  intros He1. repeat constructor. apply AppT with (Typ r). apply VarT. apply AppT with (Arr (Typ r) (Typ r)). apply AppT with (Typ r). 
  assert ((Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))) = subst_t_t (Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))) (Typ r) r).
  { simpl. destruct (var_dec r r); try contradiction. reflexivity. }
  rewrite H. apply App2T. 
  - apply He1. 
  - apply TypT.
  - rewrite insert_commute. apply VarT. inversion 1.
  - apply VarT.
Qed.

