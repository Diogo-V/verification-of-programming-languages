Require Import String.
Require Import Lia.

Require Import List.
Import ListNotations.

Open Scope string_scope.

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Fixpoint size (e: arith): nat :=
  match e with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + size e1 + size e2
  | Times e1 e2 => 1 + size e1 + size e2
  end.

Fixpoint depth (e: arith): nat :=
  match e with
  | Const _ => 1
  | Var _ => 1
  | Plus e1 e2 => 1 + max (depth e1) (depth e2)
  | Times e1 e2 => 1 + max (depth e1) (depth e2)
  end.

Theorem depth_le_size : forall e, depth e <= size e.
Proof.
  induction e. 
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. lia.
  + simpl. lia.
Qed.

Fixpoint commuter (e: arith): arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

Theorem size_commuter : forall e, size (commuter e) = size e.
Proof.
  induction e; simpl.
  + reflexivity.
  + reflexivity.
  + lia.
  + lia.
Qed.

Theorem depth_commuter : forall e, depth (commuter e) = depth e.
Proof.
  induction e; simpl; lia.
Qed.

Theorem commuter_inverse : forall e, commuter (commuter e) = e.
Proof.
  induction e; simpl.
  + reflexivity.
  + reflexivity.
  + rewrite IHe1. rewrite IHe2. reflexivity.
  + rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Infix "=?" := string_dec.

Fixpoint substitute (inThis: arith) (replaceThis: string) (withThis: arith): arith :=
  match inThis with
  | Const n => Const n
  | Var x => if x =? replaceThis then withThis else Var x
  | Plus e1 e2 => Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 => Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

Theorem substitute_depth : forall replaceThis withThis inThis, 
  depth (substitute inThis replaceThis withThis)
  <= depth inThis + depth withThis.
Proof.
  induction inThis; simpl.
  + lia.
  + destruct (x =? replaceThis).
  ++ lia.
  ++ simpl. lia.
  + lia.
  + lia.
Qed.

Theorem substitute_depth_snazzy : forall replaceThis withThis inThis,
  depth (substitute inThis replaceThis withThis)
  <= depth inThis + depth withThis.
Proof.
  induction inThis; simpl; try lia.
  + destruct (x =? replaceThis); simpl; lia.
Qed.

Theorem substitute_self : forall replaceThis inThis,
  substitute inThis replaceThis (Var replaceThis) = inThis.
Proof.
  induction inThis; simpl; try reflexivity.
  + destruct (x =? replaceThis).
  ++ rewrite e. reflexivity.
  ++ reflexivity.
  + rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  + rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

Theorem substitute_commuter : forall replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
  = substitute (commuter inThis) replaceThis (commuter withThis).
Proof.
  induction inThis; simpl; try reflexivity.
  + destruct (x =? replaceThis); reflexivity.
  + rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  + rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

