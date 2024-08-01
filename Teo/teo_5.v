Require Import String.
Require Import Lia.

Require Import List.
Import ListNotations.

Require Import Maps.
Require Import Coq.Unicode.Utf8_core.

Open Scope string_scope.

Inductive arith: Set :=
| Const (n: nat)
| Var (x: string)
| Plus (e1 e2: arith)
| Times (e1 e2: arith).

Example ex1: arith := Plus (Const 2) (Times (Var "x") (Const 1)).

Fixpoint depth (e: arith): nat :=
  match e with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + max (depth e1) (depth e2)
  | Times e1 e2 => 1 + max (depth e1) (depth e2)
  end.

Fixpoint size (e: arith): nat := 
  match e with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + size e1 + size e2
  | Times e1 e2 => 1 + size e1 + size e2
  end.

Theorem depth_le_size: forall e, depth e <= size e.
Proof.
  induction e; simpl; lia.
Qed.

Fixpoint subst (e: arith) (x: string) (e': arith): arith :=
  match e with
  | Const n => Const n
  | Var y => if string_dec x y then e' else Var y
  | Plus e1 e2 => Plus (subst e1 x e') (subst e2 x e')
  | Times e1 e2 => Times (subst e1 x e') (subst e2 x e')
  end.

Fixpoint getValue (env: list (string * nat)) (x: string): nat :=
  match env with
  | [] => 0
  | (y, n) :: env' => if string_dec x y then n else getValue env' x
  end.

Fixpoint eval (e: arith) (env: list (string * nat)): nat :=
  match e with
  | Const n => n
  | Var x => getValue env x
  | Plus e1 e2 => eval e1 env + eval e2 env
  | Times e1 e2 => eval e1 env * eval e2 env
  end.

Compute eval ex1 [("x", 3)].

(* Maps *)

Infix "=?" := string_dec.
Notation var := string.
Definition valuation := partial_map nat.

Example m1 := "x" |-> 0.
Compute m1 "x".

Example m1 "v".
Example m2 := "x" |-> 1; m1.
Compute m2 "x".

Example m3 := "y" |-> 3; m2.
Compute m3 "x".
             
Close Scope string_scope.