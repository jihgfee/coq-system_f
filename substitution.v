Require Import syntax.
From stdpp Require Import gmap.

Global Instance type_dec : EqDecision type.
Proof. solve_decision. Qed.

Fixpoint FVE e : gset var := 
  match e with
  | Var x => {[x]} 
  | Lam x t e => FVE e ∖ {[x]}
  | App e1 e2 => FVE e1 ∪ FVE e2
  | Lam2 t e => FVE e
  | App2 e t => FVE e
  end.

Fixpoint BVE e : gset var :=
 match e with
  | Var x => ∅
  | Lam x t e => BVE e ∪ {[x]}
  | App e1 e2 => BVE e1 ∪ BVE e2
  | Lam2 t e => BVE e
  | App2 e t => BVE e
  end.

Fixpoint subst_e_e e' e x : expr :=
  match e' with
  | Var x' => if decide (x' = x) then e else Var x' 
  | Lam y tau e'' => if decide (y <> x /\ (y ∉ FVE e)) then Lam y tau (subst_e_e e'' e x) else Lam y tau e''
  | App e1 e2 => App (subst_e_e e1 e x) (subst_e_e e2 e x)
  | Lam2 t e'' => Lam2 t (subst_e_e e'' e x)
  | App2 e'' tau => App2 (subst_e_e e'' e x) tau
  end.

Lemma difference_nin (x y : var) (s : gset var) : x ∈ s -> y ≠ x -> x ∈ s ∖ {[y]}.
Proof.
  intros.
  apply elem_of_difference. split.
  - apply H.
  - unfold not. intros. apply H0. apply elem_of_singleton in H1. rewrite H1. reflexivity.
Qed.

Lemma none_subst_e e' e x : x ∉ FVE e' -> subst_e_e e' e x = e'.
Proof.
  intros HIn. 
  induction e'. 
  - simpl. destruct (decide (x0 = x)).
    + unfold not in HIn. assert (False). { apply HIn. subst. simpl. apply elem_of_singleton. reflexivity. } contradiction.
    + reflexivity. 
  - simpl. destruct (decide (x0 ≠ x ∧ (x0 ∉ (FVE e)))).
    + destruct a. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply difference_nin. apply H1. unfold not. apply H.
    + reflexivity. 
  - simpl. rewrite IHe'1. rewrite IHe'2. reflexivity.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply H.
  - simpl. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply H.
Qed.

(* Type Substitution *)
Fixpoint FVT t : gset var :=
  match t with
  | Typ t => {[t]}
  | Arr tau1 tau2 => FVT tau1 ∪ FVT tau2
  | All t tau => FVT tau ∖  {[t]}
  end. 

Fixpoint BVT t : gset var :=
  match t with
  | Typ t => ∅
  | Arr tau1 tau2 => BVT tau1 ∪ BVT tau2
  | All t tau => BVT tau ∪ {[t]}
  end.

Fixpoint subst_t_t (tau':type) (tau:type) t : type :=
  match tau' with
  | Typ t' => if decide (t = t') then tau else tau'
  | Arr tau1 tau2 => Arr (subst_t_t tau1 tau t) (subst_t_t tau2 tau t)
  | All t' tau'' => if decide (t <> t' /\ t' ∉ FVT tau) then All t' (subst_t_t tau'' tau t) else All t' tau''
  end.

Lemma none_subst_t tau' tau t : t ∉ FVT tau' -> subst_t_t tau' tau t = tau'.
Proof.
  intros HIn. 
  induction tau'.
  - simpl. destruct (decide (t = t0)).
    + subst. unfold not in HIn. assert (False). { apply HIn. simpl. apply elem_of_singleton. reflexivity. } contradiction.
    + reflexivity.
  - simpl. rewrite IHtau'1. rewrite IHtau'2. reflexivity.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. destruct (decide (t ≠ t0 ∧ t0 ∉ FVT tau)).
    + destruct a. rewrite IHtau'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply elem_of_difference. split. apply H1. unfold not. intros. apply H. apply elem_of_singleton in H2. rewrite H2. reflexivity.
    + reflexivity.
Qed.

(* Type/Expressions *)
Fixpoint FVET e : gset var := 
  match e with
  | Var x => ∅
  | Lam x tau e => FVET e ∪ FVT tau 
  | App e1 e2 => FVET e1 ∪ FVET e2
  | Lam2 t e => FVET e ∖ {[t]}
  | App2 e tau => FVET e ∪ FVT tau 
  end.

Fixpoint BVET e : gset var :=
 match e with
  | Var x => ∅
  | Lam x tau e => BVET e ∪ BVT tau
  | App e1 e2 => BVET e1 ∪ BVET e2
  | Lam2 t e => {[t]} ∪ BVE e
  | App2 e tau => BVE e ∪ BVT tau
  end.

Fixpoint subst_e_t e' (tau:type) (t:var) :=
  match e' with
  | Var x => Var x
  | Lam x tau' e => Lam x (subst_t_t tau' tau t) (subst_e_t e tau t)
  | App e1 e2 => App (subst_e_t e1 tau t) (subst_e_t e2 tau t) 
  | Lam2 t' e => if decide (t <> t' /\ t' ∉ FVET e) then Lam2 t' (subst_e_t e tau t) else Lam2 t' e
  | App2 e tau' => App2 (subst_e_t e tau t) (subst_t_t tau' tau t)
  end.

Lemma none_subst_et e tau t : t ∉ FVET e -> subst_e_t e tau t = e.
Proof.
  intros HIn. 
  induction e.
  - simpl. reflexivity.
  - simpl. rewrite IHe. rewrite none_subst_t. reflexivity.
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. destruct (decide (t ≠ t0 ∧ t0 ∉ FVET e)).
    + rewrite IHe. reflexivity. destruct a. simpl in HIn. unfold not in *. intros. apply HIn. simpl. apply elem_of_difference. split. apply H1. unfold not. intros. apply H. apply elem_of_singleton in H2. rewrite H2. reflexivity.
    + reflexivity.
  - simpl. rewrite IHe. rewrite none_subst_t. reflexivity. 
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
Qed.