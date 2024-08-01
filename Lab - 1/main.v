(* Exercise 1 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition weekday_to_nat(d: day): nat := 
  match d with
    | monday => 1
    | tuesday => 2
    | wednesday => 3
    | thursday => 4
    | friday => 5
    | saturday => 6
    | sunday => 7
  end.

Compute weekday_to_nat friday.

Definition is_weekend(d: day): bool :=
  match d with
    | saturday => true
    | sunday => true
    | _ => false
  end.

Compute is_weekend monday.

(* Exercise 2 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.


Definition negb(b: bool) := 
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1: bool) (b2: bool): bool :=
  match b1 with 
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool): bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "~ x" := (negb x).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition xor (b1: bool) (b2: bool): bool :=
  match b1 with
  | true => ~b2
  | false => b2
  end.


Example test_xor1: (xor true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor2: (xor true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_xor3: (xor false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor4: (xor false false) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise 3 *)

Module NatPlayground.

Inductive nat: Type :=
  | O: nat
  | S : nat -> nat.

Definition minustwo (n: nat): nat :=
  match n with
  | O => n
  | S O => O
  | S (S n') => n'
  end.

Fixpoint evenb (n: nat): bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => evenb n'
  end.

Definition oddb (n: nat): bool := negb (evenb n).

Require Import Arith.

Fixpoint plus (n m: nat): nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
  
Fixpoint mult (n m: nat): nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Fixpoint exp (base power: nat): nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint minus (n m: nat): nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n' , S m' => minus n' m'
  end.

Fixpoint factorial (n: nat): nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

End NatPlayground.
