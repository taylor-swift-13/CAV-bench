(* Given length of a side and high return area for a triangle.
>>> triangle_area(5, 3)
7.5 *)

(* Spec(side : float, high : float, output : float) :=
	output = side * high / 2 *)

Require Import Reals.
Open Scope R_scope.

(* Pre: side and high should be non-negative for a valid triangle area *)
Definition problem_45_pre (side high : R) : Prop := side >= 0 /\ high >= 0.

Definition problem_45_spec(side high output : R) : Prop :=
	output = side * high / 2.

Require Import ZArith.
Definition problem_45_pre_z (a h : Z) : Prop :=
  (0 <= a)%Z /\ (0 <= h)%Z.

(* The integer output is the exact numerator of the area over denominator 2. *)
Definition problem_45_spec_twice_z (a h output : Z) : Prop :=
  output = (a * h)%Z.
