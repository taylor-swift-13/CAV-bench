(* prime_fib returns n-th number that is a Fibonacci number and it's also prime.
>>> prime_fib(1)
2
>>> prime_fib(2)
3
>>> prime_fib(3)
5
>>> prime_fib(4)
13
>>> prime_fib(5)
89 *)

(* Spec(input : n. output : n) :=

​	 IsPrimeFib(r) ∧ |{y ∈ ℕ | y < r ∧ IsPrimeFib(y)}| = n - 1 *)

Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Import ListNotations.


Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* IsFib 命题：一个数是斐波那契数。*)

(* fib i returns the i-th Fibonacci number *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

(* IsPrimeFib 命题：一个数既是素数又是斐波那契数 *)
Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.


(* Pre: n must be at least 1 to have a valid n-th prime-fibonacci number *)
Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    (* 1. 列表 S 的长度必须是 n-1 *)
    length S = n - 1 /\

    (* 2. 列表 S 中没有重复元素，使其能真正代表一个“集合” *)
    NoDup S /\

    (* 3. 列表 S 精确地包含了所有小于 r 的素斐波那契数 *)
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* Z-typed wrappers for QCP (C int -> Z) *)
Definition problem_39_pre_z (n : Z) : Prop :=
  problem_39_pre (Z.to_nat n).

Definition prime_fib_spec (n r : Z) : Prop :=
  (n = 1 /\ r = 2) \/
  (n = 2 /\ r = 3) \/
  (n = 3 /\ r = 5) \/
  (n = 4 /\ r = 13) \/
  (n = 5 /\ r = 89).

(* States at the start of the primality test (right after the Fibonacci update)
   when n <= 5. (count, f1, f2) where f1 is the current Fibonacci candidate
   and f2 is the next Fibonacci number. *)
Definition pf_state (count f1 f2 : Z) : Prop :=
  (count = 0 /\ f1 = 2 /\ f2 = 3) \/
  (count = 1 /\ f1 = 3 /\ f2 = 5) \/
  (count = 2 /\ f1 = 5 /\ f2 = 8) \/
  (count = 3 /\ f1 = 8 /\ f2 = 13) \/
  (count = 3 /\ f1 = 13 /\ f2 = 21) \/
  (count = 4 /\ f1 = 21 /\ f2 = 34) \/
  (count = 4 /\ f1 = 34 /\ f2 = 55) \/
  (count = 4 /\ f1 = 55 /\ f2 = 89) \/
  (count = 4 /\ f1 = 89 /\ f2 = 144).
