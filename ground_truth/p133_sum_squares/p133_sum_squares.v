(* def sum_squares(lst):
You are given a list of numbers.
You need to return the sum of squared numbers in the given list,
round each element in the list to the upper int(Ceiling) first.
Examples:
For lst = [1,2,3] the output should be 14
For lst = [1,4,9] the output should be 98
For lst = [1,3,5,7] the output should be 84
For lst = [1.4,4.2,0] the output should be 29
For lst = [-2.4,1,1] the output should be 6 *)
Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.

Open Scope R_scope.
(* z 是 x 的 ceiling 的一个等价刻画： IZR z - 1 < x <= IZR z *)
Definition is_ceil (x : R) (z : Z) : Prop :=
  (IZR z - 1 < x) /\ (x <= IZR z).

(* 任意实数列表均可 *)
Definition problem_133_pre (lst : list R) : Prop := True.

(* 规约：对于输入实数列表 lst，输出 s 为对应每个元素向上取整后的整数的平方和 *)
Definition problem_133_spec (lst : list R) (s : Z) : Prop :=
  exists zs : list Z,
    Forall2 is_ceil lst zs /\
    s = fold_right Z.add 0%Z (map (fun z => Z.mul z z) zs).

(* QCP 2.0.4 finite-float adapter. *)
Require Import SimpleC.SL.FloatLib.
Definition problem_133_pre_fp32 (input : list fp32) : Prop :=
  Forall fp32_isFinite input.
Definition problem_133_spec_fp32 (input : list fp32) (output : Z) : Prop :=
  problem_133_spec (map fp32_to_R_total input) output.

Open Scope Z_scope.

Definition ceil_ratio_133 (numerator denominator : Z) : Z :=
  let q := Z.quot numerator denominator in
  let r := Z.rem numerator denominator in
  if 0 <? r then q + 1 else q.

Fixpoint sum_squares_ratio_133 (nums dens : list Z) : Z :=
  match nums, dens with
  | n :: ns, d :: ds =>
      let z := ceil_ratio_133 n d in
      z * z + sum_squares_ratio_133 ns ds
  | _, _ => 0
  end.

Definition problem_133_prefix_z
    (nums dens : list Z) (i sum : Z) : Prop :=
  sum =
    sum_squares_ratio_133
      (firstn (Z.to_nat i) nums)
      (firstn (Z.to_nat i) dens).

Definition problem_133_pre_z (nums dens : list Z) : Prop :=
  Zlength nums = Zlength dens /\
  forall i, 0 <= i < Zlength nums ->
    let n := Znth i nums 0 in
    let d := Znth i dens 0 in
    let q := Z.quot n d in
    let r := Z.rem n d in
    let z := ceil_ratio_133 n d in
    0 < d /\
    (0 < r -> q < 2147483647) /\
    -2147483648 <= z <= 2147483647 /\
    -2147483648 <= z * z <= 2147483647 /\
    -2147483648 <=
      sum_squares_ratio_133
        (firstn (Z.to_nat (i + 1)) nums)
        (firstn (Z.to_nat (i + 1)) dens)
      <= 2147483647.

Definition problem_133_spec_z
    (nums dens : list Z) (output : Z) : Prop :=
  output = sum_squares_ratio_133 nums dens.
