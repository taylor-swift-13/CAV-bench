(* def sorted_list_sum(lst):
"""Write a function that accepts a list of strings as a parameter,
deletes the strings that have odd lengths from it,
and returns the resulted list with a sorted order,
The list is always a list of strings and never an array of numbers,
and it may contain duplicates.
The order of the list should be ascending by length of each word, and you
should return the list sorted by that rule.
If two words have the same length, sort the list alphabetically.
The function should return a list of strings in sorted order.
You may assume that all words will have the same length.
For example:
assert list_sort(["aa", "a", "aaa"]) => ["aa"]
assert list_sort(["ab", "a", "aaa", "cd"]) => ["ab", "cd"]
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation Coq.Sorting.Sorted Coq.Structures.OrderedTypeEx.
Import ListNotations.

Definition lex_le (s1 s2 : string) : Prop :=
  String_as_OT.lt s1 s2 \/ s1 = s2.

Definition string_le (s1 s2 : string) : Prop :=
  String.length s1 < String.length s2 \/
  String.length s1 = String.length s2 /\ lex_le s1 s2.

Definition has_even_length (s : string) : bool := Nat.even (length s).

(* 任意字符串列表输入均可 *)
Definition problem_149_pre (input : list string) : Prop := True.

Definition problem_149_spec (input : list string) (output : list string) : Prop :=
  Permutation output (filter has_even_length input) /\
  StronglySorted string_le output.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.
Import naive_C_Rules.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.

Definition ascii_of_z_149 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_149 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_149 c) (string_of_list_z_149 rest)
  end.

Definition row_payload_z_149 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_149 (row : list Z) : string :=
  string_of_list_z_149 (row_payload_z_149 row).

Definition rows_to_strings_z_149 (rows : list (list Z)) : list string :=
  map row_string_z_149 rows.

Definition rows_length (rows : list (list Z)) : Z :=
  Zlength rows.

Definition ptrs_length (ptrs : list Z) : Z :=
  Zlength ptrs.

Definition rows_length_149 := rows_length.

Definition ptrs_length_149 := ptrs_length.

Definition row_len_z_149 (row : list Z) : Z :=
  string_lib.string_length (row_payload_z_149 row).

Definition even_row_z_149 (row : list Z) : bool :=
  Z.even (row_len_z_149 row).

Fixpoint filter_even_rows_149 (rows : list (list Z)) : list (list Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      if even_row_z_149 row
      then row :: filter_even_rows_149 rest
      else filter_even_rows_149 rest
  end.

Definition filter_even_prefix_149 (rows : list (list Z)) (k : Z) : list (list Z) :=
  filter_even_rows_149 (firstn (Z.to_nat k) rows).

Definition filter_even_state_149
    (rows : list (list Z)) (k : Z) (output_rows : list (list Z)) : Prop :=
  0 <= k <= Zlength rows /\
  output_rows = filter_even_prefix_149 rows k.

Definition string_rows_sorted (rows : list (list Z)) : Prop :=
  StronglySorted string_le (rows_to_strings_z_149 rows).

Definition string_rows_sorted_149 := string_rows_sorted.

Definition Permutation_rows_149 (a b : list (list Z)) : Prop :=
  Permutation a b.

Definition problem_149_pre_z (rows : list (list Z)) : Prop :=
  problem_149_pre (rows_to_strings_z_149 rows).

Definition problem_149_spec_z
    (rows : list (list Z)) (output_rows : list (list Z)) : Prop :=
  problem_149_spec (rows_to_strings_z_149 rows) (rows_to_strings_z_149 output_rows).

Definition rows_well_formed_149 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  n < INT_MAX /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_149 row in
    row = string_lib.c_string payload /\
    string_lib.valid_string payload /\
    string_lib.string_length payload < INT_MAX.

Definition filter_even_step_keep_149
    (rows : list (list Z)) (i : Z) (output_rows : list (list Z)) : Prop :=
  filter_even_state_149 rows (i + 1) output_rows.

Definition filter_even_step_take_149
    (rows : list (list Z)) (i : Z)
    (output_rows output_rows_next : list (list Z)) : Prop :=
  output_rows_next = output_rows ++ [Znth i rows nil] /\
  filter_even_state_149 rows (i + 1) output_rows_next.

Definition problem_149_spec_z_of_sorted_filter
    (rows filtered sorted : list (list Z)) : Prop :=
  filter_even_state_149 rows (Zlength rows) filtered ->
  Permutation_rows_149 filtered sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.

Definition problem_149_spec_z_of_sorted_prefix
    (rows sorted : list (list Z)) : Prop :=
  Permutation_rows_149 (filter_even_prefix_149 rows (Zlength rows)) sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.
