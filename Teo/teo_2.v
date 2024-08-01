Fixpoint beq_nat (n m: nat): bool :=
  match n, m with
  | O, O => true
  | O, S m' => false
  | S n', O => false
  | S n', S m' => beq_nat n' m'
  end.

Fixpoint leb (n m: nat): bool :=
  match n, m with
  | O, _ => true
  | S n', O => false
  | S n', S m' => leb n' m'
  end.

Example test1: (leb 1 2) = true.
Proof. simpl. reflexivity. Qed.

Inductive natprod: Type :=
  | pair: nat -> nat -> natprod.

Check pair 3 5.

Definition fst (p: natprod): nat :=
  match p with
  | pair n1 n2 => n1
  end.

Example test1_fst: (fst (pair 1 2)) = 1.
Proof. simpl. reflexivity. Qed.

Definition snd (p: natprod): nat :=
  match p with
  | pair n1 n2 => n2
  end.

Example test1_snd: (snd (pair 3 5)) = 5.
Proof. simpl. reflexivity. Qed.

Notation "( x , y )" := (pair x y).

Check (3,4).

Definition swap_pair (p: natprod): natprod :=
  match p with
  | (n, m) => (m, n)
  end.

Example test1_swap: (swap_pair (3, 5)) = (5, 3).
Proof. simpl. reflexivity. Qed.

Lemma swap_twice: forall (n m: nat),
  swap_pair (swap_pair (n, m)) = (n,  m).
Proof. intros. simpl. reflexivity. Qed.

Inductive natlist: Type :=
  | nil_: natlist
  | cons_: nat -> natlist -> natlist.

Definition mylist := cons_ 1 (cons_ 2 (cons_ 3 nil_)).

Fixpoint length (l: natlist): nat :=
  match l with
  | nil_ => 0
  | cons_ n l' => 1 + length l'
  end.

Example test1_length: length mylist = 3.
Proof. simpl. reflexivity. Qed.  

Inductive natoption: Type :=
  | Some: nat -> natoption
  | None: natoption.

Inductive list (X: Type): Type :=
  | nil: list X
  | cons: X -> list X -> list X.

Check list.
Check nil nat.
Check cons.
Check cons nat.
Check cons bool.
Check (cons nat 3 (nil nat)).

Fixpoint repeat (T: Type) (v: T) (count: nat): list T :=
  match count with
  | 0 => nil T
  | S n => cons T v (repeat T v n)
  end.

Compute (repeat nat 3 0).

Arguments nil {X}.
Arguments cons {X}.

Check (cons true (cons false nil)).

Fixpoint repeat_ {T: Type} (v: T) (count: nat): list T :=
  match count with
  | 0 => nil
  | S n => cons v (repeat_ v n)
  end.

Compute repeat_ 1 4.
