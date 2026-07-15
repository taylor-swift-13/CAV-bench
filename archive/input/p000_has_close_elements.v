(* Check if in given list of numbers, are any two numbers closer to each other than
given threshold.
>>> has_close_elements([1.0, 2.0, 3.0], 0.5)
False
>>> has_close_elements([1.0, 2.8, 3.0, 4.0, 5.0, 2.0], 0.3)
True
*)
Require Import List Reals.
Require Import SimpleC.SL.FloatLib.
Import ListNotations.
Open Scope R_scope.

Definition problem_0_pre(threshold : R): Prop :=
  threshold >= 0.

Definition problem_0_spec (numbers : list R) (threshold : R) (output : bool): Prop :=
  (exists (i j : nat) (x y : R),
    i <> j /\
    Nat.lt i (length numbers) /\
    Nat.lt j (length numbers) /\
    nth i numbers 0 = x /\
    nth j numbers 0 = y /\
    Rabs (x - y) < threshold) <->
    output = true.

Definition problem_0_pre_fp32 (threshold : fp32) : Prop :=
  fp32_isFinite threshold /\ problem_0_pre (fp32_to_R_total threshold).

Definition problem_0_spec_fp32
    (numbers : list fp32) (threshold : fp32) (output : Z) : Prop :=
  (output = 1%Z /\
   problem_0_spec (map fp32_to_R_total numbers)
                  (fp32_to_R_total threshold) true) \/
  (output = 0%Z /\
   problem_0_spec (map fp32_to_R_total numbers)
                  (fp32_to_R_total threshold) false).
