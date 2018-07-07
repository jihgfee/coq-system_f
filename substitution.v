Require Import syntax.
From stdpp Require Import gmap.
From stdpp Require Import set.


Global Instance set_elem_dec {T} (x:T) (xs:set T) : Decision (set_elem_of x xs).
Proof. Admitted.

(* Expression substitution *)
Fixpoint FVE e := 
  match e with
  | Var x => set_singleton x 
  | Lam x t e => set_difference (FVE e) (set_singleton (x))
  | App e1 e2 => set_union (FVE e1) (FVE e2)
  | Lam2 t e => FVE e
  | App2 e t => FVE e
  end.

Fixpoint BVE e :=
 match e with
  | Var x => set_empty
  | Lam x t e => set_union (BVE e) (set_singleton (x))
  | App e1 e2 => set_union (BVE e1) (BVE e2)
  | Lam2 t e => BVE e
  | App2 e t => BVE e
  end.

Fixpoint subst_e_e e' e x :=
  match e' with
  | Var x' => if decide (x' = x) then e else Var x' 
  | Lam y t e'' => if decide (y <> x /\ (not (set_elem_of y (FVE e)))) then Lam y t (subst_e_e e'' e x) else Lam y t e''
  | App e1 e2 => App (subst_e_e e1 e x) (subst_e_e e2 e x)
  | Lam2 t e'' => Lam2 t (subst_e_e e'' e x)
  | App2 e'' t => App2 (subst_e_e e'' e x) t
  end.

Lemma none_subst_e e' e x : not (set_elem_of x (FVE e')) -> subst_e_e e' e x = e'.
Proof.
  intros HIn. 
  induction e'. 
  - simpl. destruct (decide (x0 = x)).
    + unfold not in HIn. assert (False). { apply HIn. subst. simpl. done. } contradiction.
    + reflexivity. 
  - simpl. destruct (decide (x0 ≠ x ∧ (not (set_elem_of x0 (FVE e))))).
    + destruct a. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. done.
    + reflexivity. 
  - simpl. rewrite IHe'1. rewrite IHe'2. reflexivity.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply H.
  - simpl. rewrite IHe'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply H.
Qed.

(* Type Substitution *)
Fixpoint FVT t :=
  match t with
  | Typ t => set_singleton t
  | Arr tau1 tau2 => set_union (FVT tau1) (FVT tau2)
  | All t tau => set_difference (FVT tau) (set_singleton t)
  end. 

Fixpoint BVT t :=
  match t with
  | Typ t => set_empty
  | Arr tau1 tau2 => set_union (BVT tau1) (BVT tau2)
  | All t tau => set_union (BVT tau) (set_singleton t)
  end.


Fixpoint subst_t_t (t':type) (t:type) x :=
  match t' with
  | Typ y => if decide (x = y) then t else t'
  | Arr tau1 tau2 => Arr (subst_t_t tau1 t x) (subst_t_t tau2 t x)
  | All y tau => if decide (x <> y /\ (not (set_elem_of y (FVT tau)))) then All y (subst_t_t tau t x) else All y tau
  end.


Lemma none_subst_t t' t x : not (set_elem_of x (FVT t')) -> subst_t_t t' t x = t'.
Proof.
  intros HIn. 
  induction t'.
  - simpl. destruct (decide (x = t0)).
    + subst. unfold not in HIn. assert (False). { apply HIn. done. } contradiction.
    + reflexivity.
  - simpl. rewrite IHt'1. rewrite IHt'2. reflexivity.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. right. apply H.
    + unfold not in *. intros. apply HIn. simpl. apply elem_of_union. left. apply H.
  - simpl. destruct (decide (x ≠ t0 ∧ ¬ set_elem_of t0 (FVT t'))).
    + destruct a. rewrite IHt'. reflexivity. unfold not in *. intros. apply HIn. simpl. apply elem_of_difference. split. apply H1. unfold not. intros. apply H. done.
    + reflexivity.
Qed.

Fixpoint subst_e_t (e':expr) (t:type) (x:var) := e'.

(* Fixpoint subst_e_t e' (t:type) (x:var) := *)
(*   match e' with *)
(*   | Var x' => e' *)
(*   | Lam t x e => e' *)
(*   | App e1 e2 => e' *)
(*   | Lam2 t e => e' *)
(*   | App2 e t => e' *)
(*   end. *)