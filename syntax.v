From stdpp Require Import gmap.

Definition var := positive.
Global Instance var_dec : EqDecision var.
Proof. solve_decision. Qed.

(* Pg. 140 *)

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

Global Instance type_dec : EqDecision type.
Proof. solve_decision. Qed.

Instance type_countable : Countable type.
Proof.
 set (enc := fix go e :=
  match e with
  | Typ t => GenLeaf t
  | Arr tau1 tau2 => GenNode 0 [go tau1; go tau2]
  | All t tau => GenNode 1 [GenLeaf t; go tau]
  end).
 set (dec := fix go e :=
  match e with
  | GenLeaf t => Typ t
  | GenNode 0 [tau1; tau2] => Arr (go tau1) (go tau2)
  | GenNode 1 [GenLeaf t; tau] => All t (go tau)
  | _ => Typ (xH)                  (* Dummy  *)
  end).
 refine (inj_countable' enc dec _). intros e. induction e; f_equal/=; auto.
Qed.
