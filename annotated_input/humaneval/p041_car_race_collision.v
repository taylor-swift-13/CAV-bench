(* Imagine a road that's a perfectly straight infinitely long line.
n cars are driving left to right; simultaneously, a different set of n cars
are driving right to left. The two sets of cars start out being very far from
each other. All cars move in the same speed. Two cars are said to collide
when a car that's moving left to right hits a car that's moving right to left.
However, the cars are infinitely sturdy and strong; as a result, they continue moving
in their trajectory as if they did not collide.

This function outputs the number of such collisions. *)

(* Spec(input : int, output : int) :=

​	output = input * input *)

Require Import Arith.
(* Pre: no special constraints for this numeric square function *)
Definition problem_41_pre (input : nat) : Prop := True.

Definition problem_41_spec(input output : nat) : Prop :=
  output = input * input.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition problem_41_spec_z (n r : Z) : Prop := problem_41_spec (Z.to_nat n) (Z.to_nat r).
