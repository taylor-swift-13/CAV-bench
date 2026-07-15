(* Given a positive floating point number, it can be decomposed into
and integer part (largest integer smaller than given number) and decimals
(leftover part always smaller than 1).

Return the decimal part of the number.
>>> truncate_number(3.5)
0.5 *)

Require Import Reals.
Require Import ZArith.
Open Scope R_scope.

Definition problem_2_pre(x : R) : Prop :=
  x > 0.

Definition problem_2_spec (x frac : R) : Prop :=
  frac = x - IZR (Int_part x) /\
  0 <= frac < 1.

Definition problem_2_pre_z (numerator denominator : Z) : Prop :=
  (0 <= numerator)%Z /\ (0 < denominator)%Z.

Definition problem_2_spec_z (numerator denominator output : Z) : Prop :=
  output = Z.modulo numerator denominator /\
  (0 <= output < denominator)%Z.
