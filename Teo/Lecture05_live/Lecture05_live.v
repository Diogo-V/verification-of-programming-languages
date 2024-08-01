(* Lecture 5 *)

Require Import Maps.
Require Import Coq.Unicode.Utf8_core.

Infix "=?" := string_dec.

Notation var := string.
Definition valuation := partial_map nat.

Example m1 := "x" |-> 0.
Compute m1 "x".

Example m2 := "x" |-> 1 ; m1.
Compute m2 "x".

Example m3 := "y" |-> 3 ; m2.
Compute m3 "x".

Inductive arith: Set :=
| Const (n: nat)
| Var (x: var)
| Plus (e1 e2: arith)
| Minus (e1 e2: arith)
| Times (e1 e2: arith).

Example ex1 := Const 42.
Example ex2 := Plus (Var "y") (Times (Var "x") (Const 42)).

Fixpoint interp (e: arith) (m: valuation): nat :=
  match e with
  | Const n => n
  | Var x => match m x with
             | None => 0
             | Some n => n
             end
  | Plus e1 e2 => interp e1 m + interp e2 m
  | Minus e1 e2 => interp e1 m - interp e2 m
  | Times e1 e2 => interp e1 m * interp e2 m
  end.

Definition valuation0: valuation := "x" |-> 17; "y" |-> 3.

Compute interp ex1 valuation0.
Compute interp ex2 valuation0.

Fixpoint substitute (inThis: arith) (replaceThis: var) (withThis: arith): arith := 
  match inThis with
  | Const _ => inThis
  | Var x => if x =? replaceThis then withThis else Var x
  | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Minus e1 e2 => Minus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

Theorem substitute_ok: ∀ v replaceThis withThis inThis, 
  interp (substitute inThis replaceThis withThis) v 
  = interp inThis (replaceThis |-> interp withThis v ; v).
Proof.
  induction inThis; simpl.
    - (* Const *) reflexivity.
    - (* Var *) destruct (x =? replaceThis).
      -- rewrite e. rewrite update_eq. reflexivity.
      -- rewrite update_neq.
        --- reflexivity.
        --- Search (_ ≠ _ -> _ ≠ _). apply not_eq_sym. apply n.
    - (* Plus *) rewrite IHinThis1. rewrite IHinThis2. reflexivity.
    - (* Minus *) rewrite IHinThis1. rewrite IHinThis2. reflexivity.
    - (* Times *) rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.