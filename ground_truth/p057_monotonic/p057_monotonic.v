(* def monotonic(l: list):
Return True is list elements are monotonically increasing or decreasing.
>>> monotonic([1, 2, 4, 20])
True
>>> monotonic([1, 20, 4, 10])
False
>>> monotonic([4, 1, 0, -10])
True
*)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Import ListNotations.


(*
 * monotonic 函数的最终程序规约。
 * 输入列表 l 和输出布尔值 b，它们之间的关系是：
 * b 为 true 当且仅当 l 是单调递增或单调递减的。
 *)
(* Pre: no special constraints for `monotonic` on integer lists *)
Definition problem_57_pre (l: list Z) : Prop := True.

Definition problem_57_spec (l: list Z) (b: bool) : Prop :=
  b = true <-> (Sorted Z.le l \/ Sorted Z.ge l).

From AUXLib Require Import ListLib.
Open Scope Z_scope.

Definition nondecreasing_57 (input : list Z) (i : Z) : Prop :=
  forall j : Z, (1 <= j < i)%Z -> (Znth (j - 1) input 0 <= Znth j input 0)%Z.

Definition nonincreasing_57 (input : list Z) (i : Z) : Prop :=
  forall j : Z, (1 <= j < i)%Z -> (Znth j input 0 <= Znth (j - 1) input 0)%Z.

Definition problem_57_pre_z (input : list Z) : Prop := input <> [].

Definition problem_57_prefix_z
    (input : list Z) (i incr decr : Z) : Prop :=
  ((incr = 1 /\ nondecreasing_57 input i) \/
   (incr = 0 /\ ~ nondecreasing_57 input i)) /\
  ((decr = 1 /\ nonincreasing_57 input i) \/
   (decr = 0 /\ ~ nonincreasing_57 input i)).

Definition problem_57_spec_z (input : list Z) (output : Z) : Prop :=
  (output = 1 /\
   (nondecreasing_57 input (Zlength input) \/
    nonincreasing_57 input (Zlength input))) \/
  (output = 0 /\
   ~ (nondecreasing_57 input (Zlength input) \/
      nonincreasing_57 input (Zlength input))).
