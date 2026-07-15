(* def triangle_area(a, b, c):
'''
Given the lengths of the three sides of a triangle. Return the area of
the triangle rounded to 2 decimal points if the three sides form a valid triangle.
Otherwise return -1
Three sides make a valid triangle when the sum of any two sides is greater
than the third side.
Example:
triangle_area(3, 4, 5) == 6.00
triangle_area(1, 2, 10) == -1 *)
(* 引入实数库 Reals 和整数库 ZArith *)
Require Import Reals.
Require Import ZArith.
Open Scope R_scope.

(*
  is_valid_triangle: 定义了三条边 (a, b, c) 何时能构成一个有效的三角形。
  条件：
  1. 所有边长都必须是正数。
  2. 任意两边之和必须大于第三边。
*)
Definition is_valid_triangle (a b c : R) : Prop :=
  a > 0 /\ b > 0 /\ c > 0 /\
  a + b > c /\ a + c > b /\ b + c > a.

(*
  heron_area: 使用海伦公式计算有效三角形的面积。
  - s 是半周长。
  - 面积是 sqrt(s * (s - a) * (s - b) * (s - c))。
  - sqrt 函数由 Reals 库提供。
*)
Definition heron_area (a b c : R) : R :=
  let s := (a + b + c) / 2 in
  sqrt (s * (s - a) * (s - b) * (s - c)).

(*
  is_rounded_to_2_decimals: 定义了什么是“四舍五入到两位小数”。
  条件：
  1. `rounded_val` 必须可以表示为某个整数除以100的结果。
  2. `rounded_val` 与 `original_val` 之间的绝对差值不应超过 0.005。
*)
Definition is_rounded_to_2_decimals (rounded_val original_val : R) : Prop :=
  (exists z : Z, rounded_val = IZR z / 100) /\
  rounded_val - /200 <= original_val /\ original_val < rounded_val + /200.

Definition problem_71_pre (a b c : R) : Prop := True.
(*
  triangle_area_spec: 这是最终的程序规约。
  它将输入 a, b, c 与输出 ret 关联起来。
  这个规约是一个逻辑析取（"或"），涵盖了两种情况：

  1. 如果 (a, b, c) 能构成一个有效三角形：
     则输出 `ret` 必须是根据海伦公式计算出的面积并四舍五入到两位小数的结果。

  2. 如果 (a, b, c) 不能构成一个有效三角形：
     则输出 `ret` 必须是 -1。
*)
Definition  problem_71_spec (a b c : R) (ret : R) : Prop :=
  (is_valid_triangle a b c /\ is_rounded_to_2_decimals ret (heron_area a b c))
  \/
  (~ (is_valid_triangle a b c) /\ ret = -1).

(* QCP 2.0.4 finite-float adapter. *)
Require Import SimpleC.SL.FloatLib.
Definition problem_71_pre_fp32 (a b c : fp32) : Prop :=
  fp32_isFinite a /\ fp32_isFinite b /\ fp32_isFinite c /\
  problem_71_pre (fp32_to_R_total a) (fp32_to_R_total b)
                 (fp32_to_R_total c).
Definition problem_71_spec_fp32 (a b c out : fp32) : Prop :=
  fp32_isFinite out /\
  problem_71_spec (fp32_to_R_total a) (fp32_to_R_total b)
                  (fp32_to_R_total c) (fp32_to_R_total out).

Open Scope Z_scope.
Definition valid_triangle_71_z (a b c : Z) : Prop :=
  0 < a /\ 0 < b /\ 0 < c /\ a + b > c /\ a + c > b /\ b + c > a.

Definition heron_radicand_71_z (a b c : Z) : Z :=
  (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c).

Definition problem_71_pre_z (a b c : Z) : Prop :=
  -2147483648 <= a + b <= 2147483647 /\
  -2147483648 <= a + c <= 2147483647 /\
  -2147483648 <= b + c <= 2147483647 /\
  -2147483648 <= a + b + c <= 2147483647 /\
  -2147483648 <= -a <= 2147483647 /\
  -2147483648 <= -a + b <= 2147483647 /\
  -2147483648 <= -a + b + c <= 2147483647 /\
  -2147483648 <= a - b <= 2147483647 /\
  -2147483648 <= a - b + c <= 2147483647 /\
  -2147483648 <= a + b - c <= 2147483647 /\
  -2147483648 <= (a + b + c) * (-a + b + c) <= 2147483647 /\
  -2147483648 <= (a + b + c) * (-a + b + c) * (a - b + c) <= 2147483647 /\
  -2147483648 <= heron_radicand_71_z a b c <= 2147483647.

Definition problem_71_spec_z (a b c output : Z) : Prop :=
  (valid_triangle_71_z a b c /\ output = heron_radicand_71_z a b c) \/
  (~ valid_triangle_71_z a b c /\ output = -1).

