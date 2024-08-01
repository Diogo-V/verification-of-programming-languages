Require Import String.
Require Import Lia.

Require Import List.
Import ListNotations.

Open Scope string_scope.

Require Import Maps.
Require Import Coq.Unicode.Utf8_core.

Infix "=?" := string_dec.

Notation var := string.
Definition valuation := partial_map nat.

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Inductive bexp: Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : arith)
  | BLe (a1 a2 : arith)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive cmd : Type :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | IfThenElse (b : bexp) (c1 c2 : cmd)
  | Repeat (e : arith) (body : cmd).

Fixpoint interp (e: arith) (v:valuation) : nat :=
  match e with
    | Const n => n
    | Var x =>
      match v x with
        | None => 0
        | Some n => n
      end
    | Plus e1 e2 => interp e1 v + interp e2 v
    | Times e1 e2 => interp e1 v * interp e2 v
  end.

Fixpoint beval (b: bexp) (v: valuation): bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (interp a1 v) (interp a2 v)
  | BLe a1 a2 => Nat.leb (interp a1 v) (interp a2 v)
  | BNot b => negb (beval b v)
  | BAnd b1 b2 => andb (beval b1 v) (beval b2 v)
  end.

Definition bool_to_bexp (b:bool) := if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.
Notation " 'test' b 'then' c1 'else' c2 " :=
  (IfThenElse b c1 c2)
        (at level 75, right associativity) : com_scope.
