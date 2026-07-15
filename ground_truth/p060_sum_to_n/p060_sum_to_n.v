(* def sum_to_n(n: int):
"""sum_to_n is a function that sums numbers from 1 to n.
>>> sum_to_n(30)
465
>>> sum_to_n(100)
5050
>>> sum_to_n(5)
15
>>> sum_to_n(10)
55
>>> sum_to_n(1)
1
""" *)
(* Pre: no special constraints for `sum_to_n` *)
Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

(* QCP-2.0.4 definition-only annotation adapters. *)
Require Import Coq.ZArith.ZArith.
Definition problem_60_pre_z (n : Z) : Prop := problem_60_pre (Z.to_nat n).
Definition problem_60_spec_z (n r : Z) : Prop := problem_60_spec (Z.to_nat n) (Z.to_nat r).
