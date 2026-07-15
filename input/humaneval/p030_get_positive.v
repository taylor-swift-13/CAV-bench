(* """Return only positive numbers in the list.
>>> get_positive([-1, 2, -4, 5, 6])
[2, 5, 6]
>>> get_positive([5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10])
[5, 3, 2, 3, 9, 123, 1]
""" *)

(* Spec(input : list float, output : list float) :=

​		∀f ∈ output, f > 0 /\
​		∀f ∈ output, f ∈ intput /\
​		∀f ∈ input, f > 0 → f ∈ output
    ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
*)


Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Import ListNotations.
Open Scope R_scope. (* 使得我们可以直接使用 > 和 0 表示实数版本 *)


Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.


(*
  定义一个“检查器”来判断一个实数是否为正数。
*)
Definition is_positive (r : R) : Prop :=
  r > 0.

(* Pre: no additional constraints for `get_positive` by default *)
Definition problem_30_pre (input : list R) : Prop := True.

Definition problem_30_spec (input : list R) (output : list R) : Prop :=
  (* 1. 保证 output 是 input 的子序列。
        这同时保证了 output 中的元素都来自 input，并且它们的相对顺序不变。
  *)
  is_subsequence output input /\

  (* 2. 定义过滤的核心逻辑。
        一个实数 r 在 output 中，当且仅当它在 input 中，并且它是一个正数。
  *)
  (forall r, In r output <-> (In r input /\ is_positive r)).

Require Import Coq.ZArith.ZArith.
Fixpoint filter_positive_30 (input : list Z) : list Z :=
  match input with
  | [] => []
  | x :: xs => if Z.ltb 0 x then x :: filter_positive_30 xs
               else filter_positive_30 xs
  end.
Definition problem_30_pre_z (input : list Z) : Prop := True.
Definition problem_30_spec_z (input output : list Z) : Prop :=
  output = filter_positive_30 input.
Definition problem_30_prefix_z (input : list Z) (i : Z) (output : list Z) : Prop :=
  output = filter_positive_30 (firstn (Z.to_nat i) input).
