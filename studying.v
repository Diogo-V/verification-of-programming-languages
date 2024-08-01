Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
      intros b c. destruct b.
      - destruct c.
        + reflexivity.
        + reflexivity.
      - destruct c.
        + reflexivity.
        + reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool, 
  andb b c = true -> c = true.
Proof.
  intros [] [] n; try reflexivity; try discriminate.
Qed.


Theorem plus_n_O : forall n:nat, 
  n = n + 0. 
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat, 
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.