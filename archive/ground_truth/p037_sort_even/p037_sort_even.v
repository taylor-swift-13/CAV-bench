(* This function takes a list l and returns a list l' such that
l' is identical to l in the odd indicies, while its values at the even indicies are equal
to the values of the even indicies of l, but sorted.
>>> sort_even([1, 2, 3])
[1, 2, 3]
>>> sort_even([5, 6, 3, 4])
[3, 6, 5, 4] *)

(* Spec(input : list int, output : list int) :=

​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), i % 2 <> 0 → output[i] = input[i]  /\
​	∀i ∈ [0, length(output)), ∃  j ∈ [0, length(intput))  i %2 = 0 -> j % 2 = 0 /\ input[j] = output[i]
​	∀i ∈ [0, length(input)), ∃  j ∈ [0, length(output))  i %2 = 0 -> j % 2 = 0 /\ output[j] = input[i] /\
​	∀i,j ∈ [0, length(input)), i,j % 2 == 0 /\ i < j → output[i] ≤ output[j] *)


Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Import ListNotations.
(* Pre: no additional constraints for `sort_even` by default *)
Definition problem_37_pre (input : list Z) : Prop := True.

(* Spec 的定义 *)
Definition problem_37_spec (input output : list Z) : Prop :=
  (* 1. input 是 output 的排列 (Permutation) *)
  Permutation input output /\

  (* 2. 如果索引 i 不能被 2 整除，则 output[i] 必须等于 input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\

  (* 3. output 中所有索引能被 2 整除的元素，必须是按索引顺序排好序的 (非递减) *)
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 2 = 0 /\ j mod 2 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

(* QCP 2.0.4 finite-float adapter. *)
Require Import Coq.Reals.Reals.
Require Import SimpleC.SL.FloatLib.
Definition problem_37_pre_fp32 (input : list fp32) : Prop :=
  Forall fp32_isFinite input.
Definition problem_37_spec_fp32 (input output : list fp32) : Prop :=
  let xs := map fp32_to_R_total input in
  let ys := map fp32_to_R_total output in
  Permutation xs ys /\
  length xs = length ys /\
  (forall i : nat, (i < length xs)%nat -> (i mod 2 <> 0)%nat ->
     nth i ys 0%R = nth i xs 0%R) /\
  (forall i j : nat,
     (i < length ys)%nat -> (j < length ys)%nat ->
     (i mod 2 = 0)%nat -> (j mod 2 = 0)%nat -> (i < j)%nat ->
     (nth i ys 0%R <= nth j ys 0%R)%R).
