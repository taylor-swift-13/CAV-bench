(* """ Filter given list of any python values only for integers
>>> filter_integers(['a', 3.14, 5])
[5]
>>> filter_integers([1, 2, 3, 'abc', {}, []])
[1, 2, 3]
""" *)

(* Spec(input : list, output : list int) :=

​	∀ i ∈ output, IsInteger(i) ∧
​	(∀ i ∈ input, IsInteger(i) → i ∈ output) ∧
​	∀ i ∈ output, i ∈ input
  ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l *)



Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.String.
Require Import ZArith.
Import ListNotations.

(*
  建模 Python 的动态类型值。
  Python 列表可以包含不同类型的值。在 Coq 中，我们需要用一个 Inductive 类型来显式地表示这种可能性。
  我们只对例子中出现的类型进行建模。
*)
Inductive py_value : Type :=
  | PyInt (n : Z)          (* 整数类型，我们用 Coq 的 Z 来表示 *)
  | PyString (s : string)    (* 字符串类型 *)
  | PyFloat                  (* 浮点数类型，这里我们不需要它的具体值 *)
  | PyDict                   (* 字典类型 *)
  | PyList.                  (* 列表类型 *)

(*
  定义一个“检查器”来判断一个值是否为整数。
  这个命题 is_int(v) 为真，当且仅当 v 是由 PyInt 构造的。
*)
Definition is_int (v : py_value) : Prop :=
  match v with
  | PyInt _ => True
  | _       => False
  end.

(*
  子列表定义
*)
Fixpoint is_subsequence {A : Type} (l1 l2 : list A) : Prop :=
  match l1, l2 with
  | [], _ => True
  | _, [] => False
  | x :: xs, y :: ys =>
      (x = y /\ is_subsequence xs ys) \/ is_subsequence l1 ys
  end.

(*
  步骤 4: 定义最终的规约 Spec。
  - input: 输入的值列表。
  - output: 函数过滤后输出的整数值列表。
*)
(* Pre: no additional constraints for `filter_integers` by default *)
Definition problem_22_pre (input : list py_value) : Prop := True.

Definition problem_22_spec (input : list py_value) (output : list py_value) : Prop :=
  (* 1. 保证 output 是 input 的子序列。
        这同时保证了 output 中的元素都来自 input，并且它们的相对顺序不变。
  *)
  is_subsequence output input /\

  (* 2. 定义过滤的核心逻辑。
        一个值 v 在 output 中，当且仅当它在 input 中，并且它是一个整数。
        我们用前面定义的 is_int 检查器作为过滤条件。
  *)
  (forall v, In v output <-> (In v input /\ is_int v)).

(* Definition-only adapter for the C tag/payload representation. *)
Fixpoint filter_integer_payloads (tags values : list Z) : list Z :=
  match tags, values with
  | tag :: tags', value :: values' =>
      if Z.eqb tag 0 then value :: filter_integer_payloads tags' values'
      else filter_integer_payloads tags' values'
  | _, _ => []
  end.

Definition problem_22_pre_c (tags values : list Z) : Prop :=
  List.length tags = List.length values /\
  Forall (fun tag => tag = 0%Z \/ tag = 1%Z \/ tag = 2%Z) tags.

Definition problem_22_spec_c
    (tags values output : list Z) : Prop :=
  output = filter_integer_payloads tags values.

Definition problem_22_prefix_c
    (tags values : list Z) (i : Z) (output : list Z) : Prop :=
  output = filter_integer_payloads
             (firstn (Z.to_nat i) tags)
             (firstn (Z.to_nat i) values).
