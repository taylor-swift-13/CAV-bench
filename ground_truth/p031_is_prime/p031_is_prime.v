(* Return true if a given number is prime, and false otherwise.
>>> is_prime(6)
False
>>> is_prime(101)
True
>>> is_prime(11)
True
>>> is_prime(13441)
True
>>> is_prime(61)
True
>>> is_prime(4)
False
>>> is_prime(1)
False
*)

(* Spec(input : int, output : bool) :=

​	output = prime(input) *)


Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* Pre: no additional constraints for `is_prime` by default *)
Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Adapt nat input + bool output to Z: r <> 0 means true *)
Definition problem_31_spec_z (n r : Z) : Prop :=
  r <> 0 <-> IsPrime (Z.to_nat n).
