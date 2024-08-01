Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint filter {X: Type} (test: X -> bool) (l: list X): (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
  end.

Fixpoint isOdd (n: nat): bool :=
  match n with
  | 0 => false
  | S O => true
  | S (S k) => isOdd k
  end.

Compute isOdd 4.

Compute filter isOdd [1;2;3].
Check length.

Definition countOddNumbers (l: list nat): nat := length (filter isOdd l).

Compute countOddNumbers [1;2;3;4;5].

(* lambda *)
Check (fun x => x + 1).

Definition doIt3Times (f: nat -> nat) (n: nat): nat := f (f (f n)).

Compute doIt3Times (fun x => x * x) 2.

Require Import Coq.Arith.PeanoNat.

Check 3 <=? 1.

Definition removeSmaller (n: nat) (l: list nat) := filter (fun x => n <=? x) l.

Compute removeSmaller 2 [1;2;3;4;5].

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Compute map (fun x => x + 1) [1;2;3;4].
Compute map isOdd [1;2;3;4].

Fixpoint fold {X Y: Type} (f: X -> Y -> Y) (l: list X) (b: Y): Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Compute fold plus [1;2;3;4] 0.
Check fold.

Definition constfun {X: Type} (x: X): nat -> X :=
  (fun (k: nat) => x).

Check constfun.
Check constfun 42.

Check plus 2.

Theorem plus_0_n: forall n: nat, 0 + n = n.
Proof. 
  intros n. simpl. reflexivity.
Qed.

Theorem plus_1_n: forall n: nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof. 
  intros n m NEqualsM.
  simpl. 
  subst.
  (* rewrite -> NEqualsM. *)
  reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o: nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
Qed.

