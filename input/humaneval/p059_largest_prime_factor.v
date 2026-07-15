(* def largest_prime_factor(n: int):
"""Return the largest prime factor of n. Assume n > 1 and is not a prime.
>>> largest_prime_factor(13195)
29
>>> largest_prime_factor(2048)
2
""" *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* 正确的库，其中定义了 prime *)

(*
 * largest_prime_factor 函数的最终正确程序规约
 *)
(* Pre: n must be > 1 and not prime for this spec to be meaningful *)
Definition problem_59_pre (n : Z) : Prop := (Z.gt n 1 /\ ~ (prime n)).

Definition problem_59_spec (n p: Z) : Prop :=
  (* 后置条件: p 必须是 n 的最大素数因子 *)
  (
    (* 1. p 是 n 的一个素数因子 *)
    prime p /\ (p | n) /\

    (* 2. p 是最大的那一个 *)
    (* 对于任何其他的素数因子 q，q 都必须小于或等于 p *)
    (forall q: Z, (prime q /\ (q | n)) -> Z.le q p)
  ).

(* QCP-2.0.4 definition-only annotation adapters. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.
Local Open Scope Z_scope.

Definition lpf_inv (n_pre n i : Z) : Prop :=
  n >= 2 /\
  n_pre mod n = 0 /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n \/ n = p) /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n -> p <= n) /\
  (forall q : Z, prime q -> q >= i -> Z.divide q n_pre -> Z.divide q n).

Definition lpf_while_inv (n_pre n i : Z) : Prop :=
  i + 1 <= 2147483647 /\
  n >= 2 /\
  i <= n /\
  n_pre mod n = 0 /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n \/ n = p) /\
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n -> p <= n) /\
  (forall q : Z, prime q -> q > i -> Z.divide q n_pre -> Z.divide q n).
