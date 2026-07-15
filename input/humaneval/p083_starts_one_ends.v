(* def starts_one_ends(n):
"""
Given a positive integer n, return the count of the numbers of n-digit
positive integers that start or end with 1.
""" *)
Require Import Arith.
Require Import PeanoNat.  (* Import the library for natural number properties, including Nat.pow *)
Import Nat.              (* This allows you to write 'pow' instead of 'Nat.pow' *)

Definition problem_83_pre (n : nat) : Prop := (n > 0)%nat.
(*
  The efficient spec using the standard library's power function.
  This is the recommended approach.
*)
Definition problem_83_spec (n : nat) (count : nat) : Prop :=
  n > 0 ->
  ( (n = 1 /\ count = 1)
    \/
    (n > 1 /\ count = 18 * pow 10 (n - 2))
  ).

(* QCP-2.0.4 definition-only annotation adapters. *)
Require Import Coq.ZArith.ZArith.

Definition problem_83_pre_z (n : Z) : Prop := problem_83_pre (Z.to_nat n).
Definition problem_83_spec_z (n r : Z) : Prop := problem_83_spec (Z.to_nat n) (Z.to_nat r).
