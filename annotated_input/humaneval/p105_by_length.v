(* Given an array of integers, sort the integers that are between 1 and 9 inclusive,
reverse the resulting array, and then replace each digit by its corresponding name from
"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".

For example:
arr = [2, 1, 1, 4, 5, 8, 2, 3]
-> sort arr -> [1, 1, 2, 2, 3, 4, 5, 8]
-> reverse arr -> [8, 5, 4, 3, 2, 2, 1, 1]
return ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]

If the array is empty, return an empty array:
arr = []
return []

If the array has any strange number ignore it:
arr = [1, -1 , 55]
-> sort arr -> [-1, 1, 55]
-> reverse arr -> [55, 1, -1]
return = ['One'] *)

(* 引入所需的Coq标准库 *)
Require Import Coq.Lists.List.      (* List 操作, 包括 Permutation *)
Require Import Coq.Strings.String.  (* String 类型 *)
Require Import Coq.ZArith.ZArith.    (* Z整数类型及其操作 *)
Require Import Coq.Sorting.Sorted.     (* 引入 Sorted 属性的定义 *)
Require Import Permutation.
Import ListNotations. (* 启用列表的 [a; b; c] 写法 *)
Open Scope Z_scope.

(*
  辅助函数 (1):
  定义一个布尔函数，用于检查一个整数 `z` 是否在 1 到 9 之间（包含边界）。
*)
Definition is_target_digit (z : Z) : bool :=
  (1 <=? z) && (z <=? 9).

(*
  辅助函数 (2):
  将一个 1 到 9 的整数转换为其对应的英文单词字符串。
*)
Definition digit_to_word (z : Z) : string :=
  match z with
  | 1 => "One"%string
  | 2 => "Two"%string
  | 3 => "Three"%string
  | 4 => "Four"%string
  | 5 => "Five"%string
  | 6 => "Six"%string
  | 7 => "Seven"%string
  | 8 => "Eight"%string
  | 9 => "Nine"%string
  | _ => ""%string
  end.
(* 输入可以包含任意整数 *)

Definition problem_105_pre (l_in : list Z) : Prop := True.

(*
  程序规约 (Program Specification):
  这是一个 Prop (命题)，它表达了输入列表 l_in 和输出列表 l_out 之间的关系。
  这次我们使用声明式的方式来定义排序。
*)
Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  (* 步骤 1: 筛选出 l_in 中所有 1 到 9 之间的整数 *)
  let l_filtered := filter is_target_digit l_in in

  (*
    步骤 2: 声明存在一个中间列表 `l_sorted`，它满足排序的属性。
    这是一种更符合Coq风格的规约写法。
  *)
  exists (l_sorted : list Z),
    (* 属性a: l_sorted 是 l_filtered 的一个排列 *)
    (Permutation l_filtered l_sorted /\
    (* 属性b: l_sorted 是根据小于等于关系升序排列的 *)
     Sorted Z.le l_sorted) /\
    (* 步骤 3 & 4: 后续步骤与之前相同，基于这个满足属性的 l_sorted 进行 *)
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition ascii_of_z_105 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_105 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_105 c) (string_of_list_z_105 rest)
  end.

Definition problem_105_pre_z (l : list Z) : Prop :=
  problem_105_pre l /\
  Forall (fun z => INT_MIN <= z <= INT_MAX) l.

Definition int_range_list_105 (l : list Z) : Prop :=
  Forall (fun z => INT_MIN <= z <= INT_MAX) l.

Definition problem_105_spec_z (input : list Z) (output_rows : list (list Z)) : Prop :=
  problem_105_spec input (map string_of_list_z_105 output_rows).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition copy_prefix_105 (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Definition one_literal_105 : string := "One"%string.
Definition two_literal_105 : string := "Two"%string.
Definition three_literal_105 : string := "Three"%string.
Definition four_literal_105 : string := "Four"%string.
Definition five_literal_105 : string := "Five"%string.
Definition six_literal_105 : string := "Six"%string.
Definition seven_literal_105 : string := "Seven"%string.
Definition eight_literal_105 : string := "Eight"%string.
Definition nine_literal_105 : string := "Nine"%string.

Definition all_digit_literals_105 : list string :=
  [one_literal_105].

Definition lit_payload_105 (s : string) : list Z :=
  StringToList s (StringLength s).

Definition digit_literal_105 (d : Z) : string :=
  match d with
  | 1%Z => one_literal_105
  | 2%Z => two_literal_105
  | 3%Z => three_literal_105
  | 4%Z => four_literal_105
  | 5%Z => five_literal_105
  | 6%Z => six_literal_105
  | 7%Z => seven_literal_105
  | 8%Z => eight_literal_105
  | 9%Z => nine_literal_105
  | _ => EmptyString
  end.

Definition digit_payload_105 (d : Z) : list Z :=
  lit_payload_105 (digit_literal_105 d).

Definition digit_ptr_105 (LM : string -> Z) (d : Z) : Z :=
  LM (digit_literal_105 d).

Definition digit_payloads_string_safe_105 : Prop :=
  string_lib.valid_string (digit_payload_105 1) /\
  string_lib.valid_string (digit_payload_105 2) /\
  string_lib.valid_string (digit_payload_105 3) /\
  string_lib.valid_string (digit_payload_105 4) /\
  string_lib.valid_string (digit_payload_105 5) /\
  string_lib.valid_string (digit_payload_105 6) /\
  string_lib.valid_string (digit_payload_105 7) /\
  string_lib.valid_string (digit_payload_105 8) /\
  string_lib.valid_string (digit_payload_105 9) /\
  string_lib.string_length (digit_payload_105 1) < INT_MAX /\
  string_lib.string_length (digit_payload_105 2) < INT_MAX /\
  string_lib.string_length (digit_payload_105 3) < INT_MAX /\
  string_lib.string_length (digit_payload_105 4) < INT_MAX /\
  string_lib.string_length (digit_payload_105 5) < INT_MAX /\
  string_lib.string_length (digit_payload_105 6) < INT_MAX /\
  string_lib.string_length (digit_payload_105 7) < INT_MAX /\
  string_lib.string_length (digit_payload_105 8) < INT_MAX /\
  string_lib.string_length (digit_payload_105 9) < INT_MAX.

Definition digit_literals_heap_105 (LM : string -> Z) : Assertion :=
  string_lib.store_string (digit_ptr_105 LM 1) (digit_payload_105 1) **
  string_lib.store_string (digit_ptr_105 LM 2) (digit_payload_105 2) **
  string_lib.store_string (digit_ptr_105 LM 3) (digit_payload_105 3) **
  string_lib.store_string (digit_ptr_105 LM 4) (digit_payload_105 4) **
  string_lib.store_string (digit_ptr_105 LM 5) (digit_payload_105 5) **
  string_lib.store_string (digit_ptr_105 LM 6) (digit_payload_105 6) **
  string_lib.store_string (digit_ptr_105 LM 7) (digit_payload_105 7) **
  string_lib.store_string (digit_ptr_105 LM 8) (digit_payload_105 8) **
  string_lib.store_string (digit_ptr_105 LM 9) (digit_payload_105 9) **
  GlobalStrings_missing LM all_digit_literals_105.

Definition target_digit_105 (z : Z) : bool :=
  Z.leb 1 z && Z.leb z 9.

Definition digit_words_between_105 (sorted_l : list Z) (lo hi : Z) : list (list Z) :=
  map digit_payload_105 (filter target_digit_105 (rev (sublist lo hi sorted_l))).

Definition digit_ptrs_between_105
    (LM : string -> Z) (sorted_l : list Z) (lo hi : Z) : list Z :=
  map (digit_ptr_105 LM) (filter target_digit_105 (rev (sublist lo hi sorted_l))).

Definition output_state_105
    (LM : string -> Z) (sorted_l : list Z) (k : Z)
    (rows : list (list Z)) (ptrs : list Z) : Prop :=
  0 <= k <= Zlength sorted_l /\
  rows = digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l) /\
  ptrs = digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l).

Definition problem_105_spec_z_of_output_state
    (input sorted_l : list Z) (output_rows : list (list Z))
    (LM : string -> Z) (output_ptrs : list Z) : Prop :=
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output_rows = digit_words_between_105 sorted_l 0 (Zlength sorted_l) ->
  output_ptrs = digit_ptrs_between_105 LM sorted_l 0 (Zlength sorted_l) ->
  problem_105_spec_z input output_rows.
