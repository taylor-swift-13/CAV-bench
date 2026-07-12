(* """ For a given number n, find the largest number that divides n evenly, smaller than n
>>> largest_divisor(15)
5
""" *)

(* Spec(input : int, output : int) :=

​	input % output = 0 /\

  output < input /\

​	∀i ∈ [1, input), input % i = 0 → i  ≤  output *)

Require Import Arith.

(* Pre: require `input >= 2` so that a largest proper divisor exists *)
Definition problem_24_pre (input : nat) : Prop := (input >= 2)%nat.

Definition problem_24_spec (input output : nat) : Prop :=
  (* 1. output 是 input 的一个因数 *)
  input mod output = 0 /\

  (* 2. output 严格小于 input *)
  output < input /\

  (* 3. 对于任何严格小于 input 的正因数 i, i 都小于等于 output *)
  (forall i : nat, 0 < i /\ i < input -> input mod i = 0 -> i <= output).

Require Import Coq.ZArith.ZArith.

Definition problem_24_pre_z (n : Z) : Prop := problem_24_pre (Z.to_nat n).
Definition problem_24_spec_z (n r : Z) : Prop := problem_24_spec (Z.to_nat n) (Z.to_nat r).
