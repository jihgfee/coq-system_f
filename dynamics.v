Require Import syntax.
Require Import substitution.
Require Import statics.
From stdpp Require Import gmap.
From stdpp Require Import set.

Inductive val :=
  | VarV (x : var)
  | LamV (x : var) (tau : type) (e : expr)
  | Lam2V (t : var) (e : expr)
  .

Fixpoint to_val (e : expr) :=
  match e with
  | Var x => Some (VarV x)
  | Lam x t e => Some (LamV x t e)
  | Lam2 t e => Some (Lam2V t e)
  | _ => None
  end.

Fixpoint of_val (v : val) :=
  match v with
  | VarV x => Var x
  | LamV x t e => Lam x t e
  | Lam2V t e => Lam2 t e
  end.

Inductive step_cbv : expr -> expr -> Prop :=
  | AppSV x tau e1 e2 v : to_val e2 = Some v -> step_cbv (App (Lam x tau e1) e2) (subst_e_e e1 e2 x)
  | AppLSV e1 e1' e2 : step_cbv e1 e1' -> step_cbv (App e1 e2) (App e1' e2)
  | AppRSV e1 e2 e2' v : to_val e1 = Some v -> step_cbv e2 e2' -> step_cbv (App e1 e2) (App e1 e2')
  | App2SV e t tau : step_cbv (App2 (Lam2 t e) tau) (subst_e_t e tau t)
  | App2MSV e e' tau : step_cbv e e' -> step_cbv (App2 e tau) (App2 e' tau)
  .

Inductive step_cbn : expr -> expr -> Prop :=
  | AppSN x tau e1 e2 v : to_val e2 = Some v -> step_cbn (App (Lam x tau e1) e2) (subst_e_e e1 e2 x)
  | AppLSN e1 e1' e2 : step_cbn e1 e1' -> step_cbn (App e1 e2) (App e1' e2)
  | App2SN e t tau : step_cbn (App2 (Lam2 t e) tau) (subst_e_t e tau t)
  | App2MSN e e' tau : step_cbn e e' -> step_cbn (App2 e tau) (App2 e' tau)
  .
