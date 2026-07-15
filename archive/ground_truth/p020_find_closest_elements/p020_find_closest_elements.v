(* """ From a supplied list of numbers (of length at least two) select and return two that are the closest to each
other and return them in order (smaller number, larger number).
>>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.2])
(2.0, 2.2)
>>> find_closest_elements([1.0, 2.0, 3.0, 4.0, 5.0, 2.0])
(2.0, 2.0)
""" *)

(* Spec(input : list float, output1 : float, output2 : float) :=

​	output1 ∈ input /\ output2 ∈ input
​	(∀ i, j ∈ [0, length(input)), i <> j →
​		 abs(output1 - output2)  ≤  abs(input[i] - input[j] )) ∧
​	ouput1 ≤ output2 *)


Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.


Import ListNotations.


Local Open Scope R_scope.

(* Pre: no additional constraints for `find_closest_elements` by default *)
Definition problem_20_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_20_spec (input : list R) (output1 output2 : R) : Prop :=
  (* 1. 前提条件：输入列表长度至少为 2 *)
  (length input >= 2)%nat /\  (* 使用 %nat 明确指出这是自然数比较 *)

  (* 2. 成员条件：output1 和 output2 必须是输入列表中的元素 *)
  In output1 input /\
  In output2 input /\

  (* 3. 顺序条件：output1 小于或等于 output2 *)
  output1 <= output2 /\

  (* 4. 最小距离条件：output1 和 output2 的差的绝对值是最小的 *)
  (forall i j : nat,
    (i < length input)%nat ->
    (j < length input)%nat ->
    i <> j ->
    Rabs (output1 - output2) <= Rabs (nth i input 0 - nth j input 0)).

(* QCP 2.0.4 finite-float adapter. *)
Require Import SimpleC.SL.FloatLib.
Definition problem_20_pre_fp32 (input : list fp32) : Prop :=
  Forall fp32_isFinite input /\
  problem_20_pre (map fp32_to_R_total input).
Definition problem_20_spec_fp32 (input output : list fp32) : Prop :=
  exists x y : fp32,
    output = x :: y :: nil /\
    fp32_isFinite x /\ fp32_isFinite y /\
    problem_20_spec (map fp32_to_R_total input)
                    (fp32_to_R_total x) (fp32_to_R_total y).
