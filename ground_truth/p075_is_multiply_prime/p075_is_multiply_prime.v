(* def is_multiply_prime(a):
"""Write a function that returns true if the given number is the multiplication of 3 prime numbers
and false otherwise.
Knowing that (a) is less then 100.
Example:
is_multiply_prime(30) == True
30 = 2 * 3 * 5
""" *)
Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* 其中定义了 prime *)
Open Scope Z_scope.


Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

(* QCP-2.0.4 definition-only annotation adapters. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Adapt bool result to Z: r <> 0 means true *)
Definition problem_75_spec_z (a r : Z) : Prop :=
  r <> 0 <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3.

Fixpoint list_prod (l : list Z) : Z :=
  match l with
  | [] => 1
  | x :: xs => x * list_prod xs
  end.

Definition mp_outer_inv (a_pre i a num : Z) : Prop :=
  a >= 2 /\
  exists l : list Z,
    Forall prime l /\
    Z.of_nat (length l) = num /\
    a_pre = list_prod l * a /\
    (forall k : Z, 2 <= k < i -> Z.rem a k <> 0 \/ a <= k).
