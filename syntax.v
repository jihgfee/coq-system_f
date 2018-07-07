From stdpp Require Import gmap.
From stdpp Require Import set.

Definition var := nat.
Global Instance var_dec : EqDecision var.
Proof. solve_decision. Qed.

Inductive type :=
  | Typ (t : var)
  | Arr (tau1 tau2 : type)
  | All (t : var) (tau : type)
  .

Inductive expr :=
  | Var (x : var)
  | Lam  (x : var) (tau : type) (e : expr)
  | App (e1 e2 : expr)
  | Lam2 (t : var) (e : expr)
  | App2 (e : expr) (tau : type)
  .