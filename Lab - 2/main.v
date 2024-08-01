(* Exercise 1 *)
Module Exerc1.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

Check d (b a 5).
Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool 5.
Check e bool true.
Check e mumble (b c 0).
Check e bool (b c 0).
Check c.

(* Exercise 2 *)
Module Exerc2.

Require Import Coq.Lists.List.
Import ListNotations.

Definition tl {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | h :: t => t
  end.

Example test_tl: (tl [1;2;3]) = [2;3].
Proof. simpl. reflexivity. Qed.

Definition removelast {T: Type} (l: list T): list T :=
  match l with
  | [] => []
  | h :: [] => []
  | h :: t => h :: removelast t
  end.

Compute removelast [1;2;3].

Definition firstn {T: Type} (n: nat) (l: list T): list T :=
  match l, n with
  | [], _ => []
  | _, O => []
  | h :: t, S n' => h :: firstn n' t
  end.

Compute firstn 1 [1;2;3;4].

Fixpoint skipn {T: Type} (n: nat) (l: list T): list T :=
  match n with
  | O => l
  | S n' => skipn n' (tail l)
  end.

Fixpoint last {T: Type} (l: list T): option T :=
  match l with
  | [] => None
  | h :: [] => Some h
  | h :: t => last t
  end.

Fixpoint seq (s l: nat): list nat :=
  match l with
  | O => []
  | S n' => s :: seq (s+1) n'
  end.

Compute seq 3 4.

Fixpoint split {X Y: Type} (l: list (X*Y)): (list X) * (list Y) :=
  match l with
  | [] => pair [] []
  | (v, y) :: t => (v :: fst (split t), y :: snd (split t))
  end.

Compute split [(1,true);(2,false);(3,true)].

Fixpoint append {X: Type} (l1 l2: list X): list X :=
  match l1 with
  | [] => l2
  | h :: t => h :: (append t l2)
  end.

Require Import Coq.Arith.PeanoNat.

Fixpoint existsb {X: Type} (f: X -> bool) (l: list X): bool :=
  match l with
  | [] => false
  | h :: t => match f h with
                | true => true
                | false => existsb f t
              end
  end.

Compute existsb (fun e => e <=? 3) [3;4;5].

Definition forallb {X: Type} (f: X -> bool) (l: list X): bool :=
  existsb (fun e => negb (f e)) l.

Compute forallb (fun e => e <=? 3) [3;4;5].