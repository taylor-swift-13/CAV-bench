(* def total_match(lst1, lst2):
'''
Write a function that accepts two lists of strings and returns the list that has
total number of chars in the all strings of the list less than the other list.

if the two lists have the same number of chars, return the first list.

Examples
total_match([], []) ➞ []
total_match(['hi', 'admin'], ['hI', 'Hi']) ➞ ['hI', 'Hi']
total_match(['hi', 'admin'], ['hi', 'hi', 'admin', 'project']) ➞ ['hi', 'admin']
total_match(['hi', 'admin'], ['hI', 'hi', 'hi']) ➞ ['hI', 'hi', 'hi']
total_match(['4'], ['1', '2', '3', '4', '5']) ➞ ['4']
'''*)
(* 引入必要的库 *)
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.

(* 允许使用列表的标准表示法，例如 [a; b; c] *)
Import ListNotations.
Open Scope string_scope.

(**
 * @spec problem_74_pre
 * @brief 程序前置条件：接受两个字符串列表作为输入。
 *)

Definition problem_74_pre (lst1 lst2 : list string) : Prop := True.

(**
 * @spec problem_74_spec
 * @brief 程序规约：选择两个字符串列表中总字符数较少的那个作为输出（若相等则选择第一个）。
 *)
Definition problem_74_spec (lst1 lst2 output : list string) : Prop :=
  let sum := fun l => fold_left (fun acc s => acc + String.length s) l 0 in
  (sum lst1 <= sum lst2 /\ output = lst1) \/
  (sum lst1 > sum lst2 /\ output = lst2).
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_74 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_74 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_74 c) (string_of_list_z_74 rest)
  end.

Definition row_payload_z_74 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_74 (row : list Z) : string :=
  string_of_list_z_74 (row_payload_z_74 row).

Definition rows_to_strings_z_74 (rows : list (list Z)) : list string :=
  map row_string_z_74 rows.

Definition row_len_z_74 (row : list Z) : Z :=
  string_length (row_payload_z_74 row).

Fixpoint rows_total_len_z_74 (rows : list (list Z)) : Z :=
  match rows with
  | [] => 0
  | row :: rest => row_len_z_74 row + rows_total_len_z_74 rest
  end.

Definition total_prefix_len_z_74 (rows : list (list Z)) (k : Z) : Z :=
  rows_total_len_z_74 (firstn (Z.to_nat k) rows).

Definition rows_well_formed_74 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  0 <= n <= 100 /\
  0 <= rows_total_len_z_74 rows <= INT_MAX /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_74 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition total_prefix_state_74
    (rows : list (list Z)) (k total : Z) : Prop :=
  0 <= k <= Zlength rows /\
  total = total_prefix_len_z_74 rows k.

Definition problem_74_pre_z (rows1 rows2 : list (list Z)) : Prop :=
  problem_74_pre (rows_to_strings_z_74 rows1) (rows_to_strings_z_74 rows2).

Definition problem_74_spec_z
    (rows1 rows2 output : list (list Z)) : Prop :=
  problem_74_spec
    (rows_to_strings_z_74 rows1)
    (rows_to_strings_z_74 rows2)
    (rows_to_strings_z_74 output).
