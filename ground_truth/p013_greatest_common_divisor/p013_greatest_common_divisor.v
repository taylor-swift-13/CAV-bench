(* """ Return a greatest common divisor of two integers a and b
>>> greatest_common_divisor(3, 5)
1
>>> greatest_common_divisor(25, 15)
5
""" *)

(* Spec(a, b, output) :=

(a mod output = 0) ∧
(b mod output = 0) ∧
(∀ x ∈ ℕ, (a mod x = 0 ∧ b mod x = 0) → x ≤ output) *)

Require Import ZArith.
Open Scope Z_scope.

(* Pre: at least one of `a` or `b` is non-zero (gcd(0,0) is undefined) *)
Definition problem_13_pre (a b : Z) : Prop :=
  a <> 0 \/ b <> 0.

Definition problem_13_spec (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, (a mod x = 0) -> (b mod x = 0) -> x > 0 -> x <= output).
