Require Import syntax.
Require Import substitution.
Require Import statics.
From stdpp Require Import gmap.

(* pg. 143-144 *)

(* Unit *)
Definition UnitType := 
  let t := gset_positive_fresh ∅ in
  All t (Arr (Typ t) (Typ t)).
Definition Unit :=
  let t := gset_positive_fresh ∅ in
  let x := gset_positive_fresh ∅ in
  Lam2 t (Lam x (Typ t) (Var x)).

Lemma UnitTypeChecks th g : WellTyped th g (Unit) (UnitType).
Proof. repeat constructor. Qed.

(* Pairs *)
Definition PairType t1 t2 := 
  let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) in
  All r (Arr (Arr t1 (Arr t2 (Typ r))) (Typ r)).
Definition Pair e1 t1 e2 t2 := 
  let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) in
  let x := gset_positive_fresh ∅ in
  Lam2 r (Lam x (Arr t1 (Arr t2 (Typ r))) (App (App (Var x) e1) e2)).
Definition PairLeft e t1 t2 := 
  let x1 := gset_positive_fresh ∅ in
  let x2 := gset_positive_fresh {[x1]} in
  App (App2 e t1) (Lam x1 t1 (Lam x2 t2 (Var x1))).
Definition PairRight e t1 t2 :=
  let x1 := gset_positive_fresh ∅ in
  let x2 := gset_positive_fresh {[x1]} in
  App (App2 e t2) (Lam x1 t1 (Lam x2 t2 (Var x2))).

Lemma PairTypeChecks th g t1 t2 e1 e2 : (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) -> WellTyped th g (Pair e1 t1 e2 t2) (PairType t1 t2).
Proof. intros He1 He2. repeat constructor. apply AppT with t2. apply AppT with t1. apply VarT. apply He1. apply He2. Qed.

Example UnitPairTypeExample th g : WellTyped th g (Pair (Unit) (UnitType) (Unit) (UnitType)) (PairType (UnitType) (UnitType)).
Proof. apply PairTypeChecks; intros; apply UnitTypeChecks. Qed.

Lemma PairLeftChecks th g e1 e2 t1 t2 : 
  WellTTyped th t1 ->
  (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) ->
  WellTyped th g (Pair e1 t1 e2 t2) (PairType t1 t2) -> 
  WellTyped th g (PairLeft (Pair e1 t1 e2 t2) t1 t2) t1.
Proof.
  intros Hth Ht1 Ht2 HPair.
  apply AppT with (Arr (t1) (Arr t2 (t1))). 
  assert (let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) : var in (Arr (Arr (t1) (Arr t2 t1)) t1) = subst_t_t (Arr (Arr (t1) (Arr t2 (Typ r))) (Typ r)) t1 r).
  { intros. simpl. destruct (decide (r = r)); try contradiction. rewrite none_subst_t. rewrite none_subst_t. reflexivity. apply fresh_nin_subseteq with (FVT t1 ∪ FVT t2). reflexivity. apply union_subseteq_r. apply fresh_nin_subseteq with (FVT t1 ∪ FVT t2). reflexivity. apply union_subseteq_l. } 
  rewrite H. apply App2T.
  - apply HPair. 
  - apply Hth. 
  - constructor. constructor. rewrite insert_commute. apply VarT. unfold not. inversion 1.
Qed.

Lemma PairRightChecks th g e1 e2 t1 t2 : 
  WellTTyped th t2 ->
  (forall th g, WellTyped th g e1 t1) -> (forall th g, WellTyped th g e2 t2) ->
  WellTyped th g (Pair e1 t1 e2 t2) (PairType t1 t2) -> 
  WellTyped th g (PairRight (Pair e1 t1 e2 t2) t1 t2) t2.
Proof.
  intros Hth Ht1 Ht2 HPair.
  apply AppT with (Arr (t1) (Arr t2 (t2))). 
  assert (let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) : var in (Arr (Arr (t1) (Arr t2 t2)) t2) = subst_t_t (Arr (Arr (t1) (Arr t2 (Typ r))) (Typ r)) t2 r).
  { intros. simpl. destruct (decide (r = r)); try contradiction. rewrite none_subst_t. rewrite none_subst_t. reflexivity. apply fresh_nin_subseteq with (FVT t1 ∪ FVT t2). reflexivity. apply union_subseteq_r. apply fresh_nin_subseteq with (FVT t1 ∪ FVT t2). reflexivity. apply union_subseteq_l. } 
  rewrite H. apply App2T.
  - apply HPair. 
  - apply Hth. 
  - constructor. constructor. apply VarT.
Qed.

(* Binary Sums *)
Definition SumType t1 t2 := 
  let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) in
  All r (Arr (Arr t1 (Typ r)) (Arr (Arr t2 (Typ r)) (Typ r))).
Definition SumLeft t1 t2 e1 := 
  let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) in
  let f1 := gset_positive_fresh (FVE(e1)) in
  let f2 := gset_positive_fresh (FVE(e1) ∪ {[f1]}) in
  Lam2 r (Lam f1 (Arr t1 (Typ r)) (Lam f2 (Arr t2 (Typ r)) (App (Var f1) (e1)))).
Definition SumRight t1 t2 e2 :=
  let r := gset_positive_fresh (FVT(t1) ∪ FVT(t2)) in
  let f1 := gset_positive_fresh (FVE(e2)) in
  let f2 := gset_positive_fresh (FVE(e2) ∪ {[f1]}) in
  Lam2 r (Lam f1 (Arr t1 (Typ r)) (Lam f2 (Arr t2 (Typ r)) (App (Var f2) (e2)))).

Lemma SumLeftTypeChecks th g t1 t2 e1 : (forall th g, WellTyped th g e1 t1) -> WellTyped th g (SumLeft t1 t2 e1) ((SumType t1 t2)).
Proof. intros He1. repeat constructor. apply AppT with t1.
  rewrite insert_commute. apply VarT. apply fresh_neq_union.
  apply He1.
Qed.

Lemma SumRightTypeChecks th g t1 t2 e2 : (forall th g, WellTyped th g e2 t2) -> WellTyped th g (SumRight t1 t2 e2) ((SumType t1 t2)).
Proof. intros He2. repeat constructor. apply AppT with t2. apply VarT. apply He2. Qed.

(* Natural Numbers *)
Definition NatType := 
  let r := gset_positive_fresh ∅ in
  All r (Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))).
Definition Z := 
  let r := gset_positive_fresh ∅ in
  let z := gset_positive_fresh ∅ in
  let s := gset_positive_fresh {[z]} in
  Lam2 r (Lam z (Typ r) (Lam s (Arr (Typ r) (Typ r)) (Var z))).
Definition Succ e :=
  let r := gset_positive_fresh ∅ in
  let z := gset_positive_fresh (FVE e) in
  let s := gset_positive_fresh (FVE e ∪ {[z]}) in
  Lam2 r (Lam z (Typ r) (Lam s (Arr (Typ r) (Typ r)) (App (Var s) (App (App (App2 e (Typ r)) (Var z)) (Var s))))).

Lemma ZChecks th g : WellTyped th g Z NatType.
Proof. repeat constructor. rewrite insert_commute. apply VarT. inversion 1. Qed.

Lemma SuccChecks th g e : let r := (gset_positive_fresh ∅) : var in (forall th g, WellTyped th g e NatType) -> WellTyped th g (Succ e) NatType.
Proof.
  intros r He1. repeat constructor. apply AppT with (Typ (r)). apply VarT. apply AppT with (Arr (Typ (r)) (Typ (r))). apply AppT with (Typ (r)). 
  assert ((Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))) = subst_t_t (Arr (Typ r) (Arr (Arr (Typ r) (Typ r)) (Typ r))) (Typ r) r).
  { simpl. destruct (decide (r = r)); try contradiction. reflexivity. }
  rewrite H. apply App2T. 
  - apply He1. 
  - apply TypT.
  - rewrite insert_commute. apply VarT. apply fresh_neq_union.
  - apply VarT.
Qed.