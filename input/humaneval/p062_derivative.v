(* def derivative(xs: list):
""" xs represent coefficients of a polynomial.
xs[0] + xs[1] * x + xs[2] * x^2 + ....
Return derivative of this polynomial in the same form.
>>> derivative([3, 1, 2, 4, 5])
[1, 4, 12, 20]
>>> derivative([1, 2, 3])
[2, 6]
""" *)
(* 引入 Coq 中关于列表和整数的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.

Open Scope Z_scope.

Definition problem_62_pre (xs : list Z) : Prop := True.
(*
  [problem_62_spec xs ys] 定义了输入列表 xs 和输出列表 ys 之间的关系。
  xs: 代表多项式 P(x) 系数的列表，其中 (nth i xs 0) 是 x^i 的系数。
  ys: 代表 P(x) 的导数 P'(x) 系数的列表。
*)
Definition problem_62_spec (xs ys : list Z) : Prop :=
  (* 1. 输出列表的长度应该是输入列表的长度减一（对于长度大于0的输入）。
     Coq 中自然数的减法 `Nat.sub` 在 0-1 时结果为 0，这恰好符合我们对空列表或单元素列表求导的结果。*)
  length ys = Nat.sub (length xs) 1 /\

  (* 2. 对于输出列表 ys 中的每一个索引 i... *)
  forall (i : nat),
    (* ...只要 i 是 ys 的一个有效索引... *)
    (i < length ys)%nat ->
    (* ...那么 ys 在 i 位置的值，等于 xs 在 i+1 位置的值乘以 (i+1)。
       这符合求导法则: d/dx (a * x^n) = n * a * x^(n-1)。
       - `nth i ys 0` 获取 ys 在索引 i 处的值（若越界则默认为0）。
       - `nth (i + 1) xs 0` 获取 xs 在索引 i+1 处的值。
       - `Z.of_nat (i + 1)` 将自然数索引 i+1 转换为整数类型以进行乘法。*)
    nth i ys 0 = (Z.of_nat (i + 1)) * (nth (i + 1) xs 0).

Fixpoint derivative_from_62 (k : Z) (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: tl => (k * x) :: derivative_from_62 (k + 1) tl
  end.

Definition derivative_62 (input : list Z) : list Z :=
  derivative_from_62 1 (tl input).

Definition problem_62_pre_z (input : list Z) : Prop :=
  input <> [] /\
  forall i, 1 <= i < Zlength input ->
    -2147483648 <= i * Znth i input 0 <= 2147483647.

Definition problem_62_spec_z (input output : list Z) : Prop :=
  output = derivative_62 input.

Definition problem_62_prefix_z (input : list Z) (i : Z) (output : list Z) : Prop :=
  output = derivative_from_62 1
    (firstn (Z.to_nat (i - 1)) (tl input)).
