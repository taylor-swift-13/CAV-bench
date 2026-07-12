(* def get_max_triples(n):
You are given a positive integer n. You have to create an integer array a of length n.
For each i (1 ≤ i ≤ n), the value of a[i] = i * i - i + 1.
Return the number of triples (a[i], a[j], a[k]) of a where i < j < k,
and a[i] + a[j] + a[k] is a multiple of 3.

Example :
Input: n = 5
Output: 1
Explanation:
a = [1, 3, 7, 13, 21]
The only valid triple is (1, 7, 13). *)
(* 引入所需的基础库 *)
Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.


(*
 * 定义函数 a(i)，对应于 Python 程序中的 a[i] = i*i - i + 1。
 * 这里的索引 i 是从 1 开始的自然数（nat）。
 * 为了避免自然数减法可能出现的问题，我们使用整数（Z）进行计算。
 *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

(*
 * 定义一个“有效三元组”的属性。
 * 一个三元组 (i, j, k) 是有效的，当且仅当它满足以下所有条件：
 * 1. 索引 i, j, k 满足 1 <= i < j < k <= n。
 * 2. 对应的值 a(i), a(j), a(k) 之和是 3 的倍数。
 *)
Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

(* 独立的输入前置条件 *)
Definition problem_147_pre (n : nat) : Prop := (n > 0)%nat.

(*
 * get_max_triples 函数的程序规约。
 * 它通过一阶逻辑描述了输入 n 和输出 output 之间的关系。
 *)
Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  (*
   * 存在一个三元组列表 l，它精确地包含了所有有效的、不重复的三元组，
   * 并且 output 是这个列表的长度。
   *)
  exists (l : list (nat * nat * nat)),
    (* 1. 列表 l 中的每一个元素 (i, j, k) 都必须是一个有效的 instill 三元组。 *)
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\

    (* 2. 所有有效的 instill 三元组 (i, j, k) 都必须在列表 l 中。 *)
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\

    (* 3. 列表 l 中没有重复的元素。 *)
    NoDup l /\

    (* 4. 函数的输出 output 必须等于列表 l 的长度。 *)
    output = length l.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.

Definition problem_147_pre_z (n : Z) : Prop :=
  0 <= n /\ problem_147_pre (Z.to_nat n).

Definition problem_147_spec_z (n output : Z) : Prop :=
  0 <= n /\ 0 <= output /\
  problem_147_spec (Z.to_nat n) (Z.to_nat output).

Definition triple_value_147 (i : Z) : Z :=
  i * i - i + 1.

Definition triple_good_bool_147 (i j k : Z) : bool :=
  Z.eqb (Z.rem (triple_value_147 i +
                triple_value_147 j +
                triple_value_147 k) 3) 0.

Definition triple_good_147 (n i j k : Z) : Prop :=
  1 <= i < j /\ j < k /\ k <= n /\
  triple_good_bool_147 i j k = true.

Fixpoint triples_k_aux_147 (n i j : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_k_aux_147 n i j fuel' +
      if triple_good_bool_147 i j (j + 1 + Z.of_nat fuel') then 1 else 0
  end.

Definition triples_k_147 (n i j k : Z) : Z :=
  triples_k_aux_147 n i j (Z.to_nat (k - (j + 1))).

Fixpoint triples_j_aux_147 (n i : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_j_aux_147 n i fuel' +
      triples_k_147 n i (i + 1 + Z.of_nat fuel') (n + 1)
  end.

Definition triples_j_147 (n i j : Z) : Z :=
  triples_j_aux_147 n i (Z.to_nat (j - (i + 1))).

Fixpoint triples_i_aux_147 (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      triples_i_aux_147 n fuel' +
      triples_j_147 n (1 + Z.of_nat fuel') (n + 1)
  end.

Definition triples_i_147 (n i : Z) : Z :=
  triples_i_aux_147 n (Z.to_nat (i - 1)).

Definition triple_nat_147 := (nat * nat * nat)%type.

Fixpoint triples_k_list_aux_147 (n i j : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_k_list_aux_147 n i j fuel' in
      let k := j + 1 + Z.of_nat fuel' in
      if triple_good_bool_147 i j k
      then prev ++ (Z.to_nat i, Z.to_nat j, Z.to_nat k) :: nil
      else prev
  end.

Fixpoint triples_j_list_aux_147 (n i : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_j_list_aux_147 n i fuel' in
      let j := i + 1 + Z.of_nat fuel' in
      prev ++ triples_k_list_aux_147 n i j (Z.to_nat (n + 1 - (j + 1)))
  end.

Fixpoint triples_i_list_aux_147 (n : Z) (fuel : nat) : list triple_nat_147 :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := triples_i_list_aux_147 n fuel' in
      let i := 1 + Z.of_nat fuel' in
      prev ++ triples_j_list_aux_147 n i (Z.to_nat (n + 1 - (i + 1)))
  end.

Definition triples_list_147 (n : Z) : list triple_nat_147 :=
  triples_i_list_aux_147 n (Z.to_nat n).
