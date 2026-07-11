(*  Filter an input list of strings only for ones that start with a given prefix.
>>> filter_by_prefix([], 'a')
[]
>>> filter_by_prefix(['abc', 'bcd', 'cde', 'array'], 'a')
['abc', 'array'] *)

(* Spec(input : list string, substring : string, output list string) :=

​	∀s ∈ output, s  ∈ input /\
​	∀s ∈ output, prefix(substring, s) /\
​	∀s ∈ input, prefix(substring, s) → s ∈ output /\
​	∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

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

(* Pre: no additional constraints for `filter_by_prefix` by default *)
Definition problem_29_pre (input : list string) : Prop := True.

Definition problem_29_spec (input : list string) (substring : string) (output : list string) : Prop :=
  (* 1. output 是 input 的一个子序列。
        这个自定义的 is_subsequence 保证了：
        - output 中的所有元素都来自 input (规约第一条)
        - output 中元素的相对顺序与 input 中一致 (规约第四条)
  *)
  is_subsequence output input /\

  (* 2. 一个字符串 s 在 output 中，当且仅当它在 input 中且满足前缀条件。
        这蕴含了：
        - output 中的所有元素都满足前缀条件 (规约第二条)
        - input 中所有满足前缀条件的元素都在 output 中 (规约第三条)
  *)
  (forall s, In s output <-> (In s input /\ String.prefix substring s = true)).
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

Definition ascii_of_z_29 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_29 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_29 c) (string_of_list_z_29 rest)
  end.

Definition row_payload_z_29 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_29 (row : list Z) : string :=
  string_of_list_z_29 (row_payload_z_29 row).

Definition rows_to_strings_z_29 (rows : list (list Z)) : list string :=
  map row_string_z_29 rows.

Definition row_len_z_29 (row : list Z) : Z :=
  string_length (row_payload_z_29 row).

Definition rows_well_formed_29 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_29 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition problem_29_pre_z (rows : list (list Z)) : Prop :=
  problem_29_pre (rows_to_strings_z_29 rows).

Definition problem_29_spec_z
    (rows : list (list Z)) (prefix : list Z) (output_rows : list (list Z)) : Prop :=
  problem_29_spec
    (rows_to_strings_z_29 rows)
    (string_of_list_z_29 prefix)
    (rows_to_strings_z_29 output_rows).

Definition prefix_match_z_29 (row : list Z) (prefix : list Z) : Prop :=
  String.prefix (string_of_list_z_29 prefix) (row_string_z_29 row) = true.

Fixpoint filter_prefix_rows_29
    (rows : list (list Z)) (prefix : list Z) : list (list Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      if String.prefix (string_of_list_z_29 prefix) (row_string_z_29 row)
      then row :: filter_prefix_rows_29 rest prefix
      else filter_prefix_rows_29 rest prefix
  end.

Definition filter_prefix_prefix_29
    (rows : list (list Z)) (prefix : list Z) (k : Z) : list (list Z) :=
  filter_prefix_rows_29 (firstn (Z.to_nat k) rows) prefix.

Definition filter_prefix_state_29
    (rows : list (list Z)) (prefix : list Z) (k : Z)
    (output_rows : list (list Z)) : Prop :=
  0 <= k <= Zlength rows /\
  output_rows = filter_prefix_prefix_29 rows prefix k.
