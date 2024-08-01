Definition two := 2.

Check two * (two + two).

Check two * two.

Definition succ (n: nat): nat := n + 1.

Definition succ_implicit n := n + 1.

Compute (succ 0).

Print "+".