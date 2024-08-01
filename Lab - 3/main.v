Require Import Coq.Lists.List.
Require Import String List.
Import ListNotations.

Definition partition {X: Type} (f: X -> bool) (l: list X): list X * list X 
  := (filter f l, filter (fun e => negb (f e)) l).

Theorem thm_simpl1: forall a b c: nat,
  a = 0 -> b*(a+b) = b*b.
Proof.
  intros a b c H.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.

Theorem thm_simpl2: forall (a b c d: nat) (f: nat -> nat -> nat),
    a = b -> c = d -> (forall x y, f x y = f y x) -> f a c = f d b.
Proof.
  intros a b c d f H1 H2 H3.
  rewrite -> H1.
  rewrite <- H2.
  rewrite -> H3.
  reflexivity.
Qed.