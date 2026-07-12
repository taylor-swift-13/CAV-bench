(* Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
>>> fizz_buzz(50)
0
>>> fizz_buzz(78)
2
>>> fizz_buzz(79)
3 *)

(* Spec(input : int, output : int) :=
  outout = $∑_{x=0}^{input-1}$ (if DivBy11Or13(x) then Num7sIn(x) else 0) *)

Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint count_digit_7_aux (k fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match k with
    | 0 => 0
    | _ =>
      (if Nat.eqb (k mod 10) 7 then 1 else 0) +
      count_digit_7_aux (k / 10) f'
    end
  end.

Definition count_digit_7 (k : nat) : nat :=
  count_digit_7_aux k k.

Definition fizz_buzz_impl (n : nat) : nat :=
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq 0 n)
    0.


(* Pre: no additional constraints for `fizz_buzz` by default *)
Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.

Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition fizzbuzz_upto (n : Z) : Z :=
  Z.of_nat (fizz_buzz_impl (Z.to_nat n)).

Definition count_digit7 (n : Z) : Z :=
  Z.of_nat (count_digit_7 (Z.to_nat n)).

Definition problem_36_spec_z (n r : Z) : Prop :=
  problem_36_spec (Z.to_nat n) (Z.to_nat r).

Local Open Scope nat_scope.

Local Open Scope Z_scope.
