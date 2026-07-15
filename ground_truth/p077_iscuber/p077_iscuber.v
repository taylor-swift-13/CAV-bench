(* def iscube(a):
'''
Write a function that takes an integer a and returns True
if this ingeger is a cube of some integer number.
Note: you may assume the input is always valid.
Examples:
iscube(1) ==> True
iscube(2) ==> False
iscube(-1) ==> True
iscube(64) ==> True
iscube(0) ==> True
iscube(180) ==> False
''' *)
Require Import ZArith.
Open Scope Z_scope.

Definition problem_77_pre (a : Z) : Prop := True.

Definition problem_77_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> (exists x : Z, a = x * x * x)).

(* QCP-2.0.4 definition-only annotation adapters. *)
(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_77_spec_z (a r : Z) : Prop :=
  r <> 0 <-> (exists x : Z, a = x * x * x).
