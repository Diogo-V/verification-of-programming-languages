(* Lab 02 *)

Module ex1.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Compute d (b a 5).      (* bad  *) *)
Compute d mumble (b a 5).  (* good *)
Compute d bool (b a 5).    (* good *)
(* Compute e bool 5.       (* bad  *) *)
Compute e bool true.       (* good *)
Compute e mumble (b c 0).  (* good *)
(* Compute e bool (b c 0). (* bad  *) *)
Compute c.                 (* good *)

End ex1.

Require Import Coq.Lists.List.
Import ListNotations.

Definition head {T: Type} (l: list T) : T :=
  match l with
  | [] => []
  | h :: t => t
  end.

Definition tl {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | h :: t => t
  end.

Compute tl [1;2;3]. (* = [2;3] *)

Fixpoint removelast {T: Type} (l: list T) : list T :=
  match l with
  | [] => []
  | h :: [] => []
  | h :: t => h :: removelast t
  end.

Compute removelast [1;2;3]. (* = [1;2] *)

Fixpoint firstn {T: Type} (n: nat) (l: list T) : list T :=
  match l with
  | [] => []
  | h :: t => match n with
              | O => []
              | S n' => h :: firstn n' t
              end
  end.

Compute firstn 3 [1;2;3;4;5]. (* = [1;2;3] *)

Fixpoint skipn {T: Type} (n: nat) (l: list T) : list T :=
  match n with
  | O => l
  | S n' => skipn n' (tail l)
  end.

Compute skipn 3 [1;2;3;4;5]. (* = [4;5] *)

Fixpoint last {T: Type} (l: list T) : option T :=
  match l with
  | [] => None
  | h :: [] => Some h
  | h :: t => last t
  end.

Compute last []. (* = None *)
Compute last [1;2;3]. (* = Some 3 *)

Fixpoint seq (start len : nat) : list nat :=
  match len with
  | O => []
  | S n' => start :: seq (start+1) n'
  end.

Compute seq 3 4. (* = [3;4;5;6] *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y: Type} (l: list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => pair [] []
  | h :: t => match h with
              | (a, b) => (a :: fst (split t), b :: snd (split t))
              end
  end. 

Compute split [(1,true);(2,false);(3,true)]. (* = ([1;2;3],[true;false;true]). *)
