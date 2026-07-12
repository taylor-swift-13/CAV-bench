(* def find_max(words):
"""Write a function that accepts a list of strings.
The list contains different words. Return the word with maximum number
of unique characters. If multiple strings have maximum number of unique
characters, return the one which comes first in lexicographical order.

find_max(["name", "of", "string"]) == "string"
find_max(["name", "enam", "game"]) == "enam"
find_max(["aaaaaaa", "bb" ,"cc"]) == ""aaaaaaa"
 *)
(* 导入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* 字典序比较 *)
Fixpoint string_le (s1 s2 : string) : Prop :=
  match s1, s2 with
  | EmptyString, _ => True
  | String _ _, EmptyString => False
  | String c1 s1', String c2 s2' =>
      (nat_of_ascii c1 < nat_of_ascii c2) \/ (c1 = c2 /\ string_le s1' s2')
  end.

(* 检查字符是否在字符串中 *)
Fixpoint string_contains (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c' s' => if Ascii.eqb c c' then true else string_contains c s'
  end.

(* 计算唯一字符数 *)
Fixpoint count_unique_chars (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' =>
      let n := count_unique_chars s' in
      if string_contains c s' then n else S n
  end.

(* 输入单词列表需非空 *)
Definition problem_158_pre (words : list string) : Prop := words <> [].

(*
  find_max 函数的程序规约 (Spec)。
*)
Definition problem_158_spec (words : list string) (result : string) : Prop :=
  In result words /\
  forall w, In w words ->
    let c_res := count_unique_chars result in
    let c_w := count_unique_chars w in
    c_res > c_w \/ (c_res = c_w /\ string_le result w).
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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

Definition ascii_of_z_158 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_158 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_158 c) (string_of_list_z_158 rest)
  end.

Definition row_payload_z_158 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_158 (row : list Z) : string :=
  string_of_list_z_158 (row_payload_z_158 row).

Definition rows_to_strings_z_158 (rows : list (list Z)) : list string :=
  map row_string_z_158 rows.

Definition row_unique_count_z_158 (row : list Z) : Z :=
  Z.of_nat (count_unique_chars (row_string_z_158 row)).

Definition problem_158_pre_z (rows : list (list Z)) : Prop :=
  problem_158_pre (rows_to_strings_z_158 rows).

Definition problem_158_spec_z (rows : list (list Z)) (best_idx : Z) : Prop :=
  problem_158_spec
    (rows_to_strings_z_158 rows)
    (row_string_z_158 (Znth best_idx rows nil)).

Definition rows_well_formed_158 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_158 row in
    row = string_lib.c_string payload /\
    string_lib.valid_string payload /\
    string_lib.string_length payload < INT_MAX /\
    (forall j,
       0 <= j <= string_lib.string_length payload ->
       Z.of_nat
         (count_unique_chars
            (string_of_list_z_158 (firstn (Z.to_nat j) payload))) <= 128) /\
    row_unique_count_z_158 row <= 128.

Definition byte_seen_158 (row : list Z) (j c : Z) : Prop :=
  0 <= c < 128 /\
  exists p, 0 <= p < j /\ Znth p (row_payload_z_158 row) 0 = c.

Definition count_scan_state_158
    (row : list Z) (j : Z) (seen_l : list Z) (unique : Z) : Prop :=
  0 <= j <= string_lib.string_length (row_payload_z_158 row) /\
  Zlength seen_l = 128 /\
  (forall c, 0 <= c < 128 ->
     (Znth c seen_l 0 = 0 /\ ~ byte_seen_158 row j c) \/
     (Znth c seen_l 0 = 1 /\ byte_seen_158 row j c)) /\
  unique =
    Z.of_nat
      (count_unique_chars
         (string_of_list_z_158
            (firstn (Z.to_nat j) (row_payload_z_158 row)))).

Definition reset_prefix_state_158 (k : Z) (seen_l : list Z) : Prop :=
  0 <= k <= 128 /\
  Zlength seen_l = 128 /\
  (forall c, 0 <= c < k -> Znth c seen_l 0 = 0).

Definition best_prefix_state_158
    (rows : list (list Z)) (k best_idx maxu : Z) : Prop :=
  0 <= k <= Zlength rows /\
  ((k = 0 /\ best_idx = 0 /\ maxu = 0) \/
   (0 < k /\
    0 <= best_idx < k /\
    maxu = row_unique_count_z_158 (Znth best_idx rows nil) /\
    (forall j,
       0 <= j < k ->
       row_unique_count_z_158 (Znth j rows nil) <= maxu) /\
    (forall j,
       0 <= j < k ->
       row_unique_count_z_158 (Znth j rows nil) = maxu ->
       string_le
         (row_string_z_158 (Znth best_idx rows nil))
         (row_string_z_158 (Znth j rows nil))))).

Definition strcmp_negative_158 (s1 s2 : list Z) (ret : Z) : Prop :=
  ret < 0 ->
  string_le (string_of_list_z_158 s1) (string_of_list_z_158 s2).

Definition row_blocks_seg_158
    (row_ptrs : list Z) (rows : list (list Z)) (lo hi : Z) : Assertion :=
  iter_sepcon
    (map CharPtrArray2.row_block
       (sublist lo hi (combine row_ptrs rows))).

Definition ptr_segments_except_two_158
    (x n lo hi : Z) (row_ptrs : list Z) : Assertion :=
  PtrArray.seg x 0 lo (sublist 0 lo row_ptrs) **
  PtrArray.seg x (lo + 1) hi (sublist (lo + 1) hi row_ptrs) **
  PtrArray.seg x (hi + 1) n (sublist (hi + 1) n row_ptrs).

Definition row_blocks_except_two_158
    (i j : Z) (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  let pairs := combine row_ptrs rows in
  if Z.ltb i j then
    iter_sepcon
      (map CharPtrArray2.row_block
         (CharPtrArray2.remove_Znth (j - 1)
            (CharPtrArray2.remove_Znth i pairs)))
  else
    iter_sepcon
      (map CharPtrArray2.row_block
         (CharPtrArray2.remove_Znth j
            (CharPtrArray2.remove_Znth i pairs))).

Definition char_ptr_array2_missing_two_158
    (x n i row_i j row_j : Z) (rows : list (list Z)) : Assertion :=
  EX row_ptrs : list Z,
    “ Zlength row_ptrs = n /\
      Zlength rows = n /\
      0 <= i < n /\
      0 <= j < n /\
      i <> j /\
      row_i = Znth i row_ptrs 0 /\
      row_j = Znth j row_ptrs 0 ” &&
    if Z.ltb i j then
      PtrArray.missing_i x j 0 n row_ptrs **
      row_blocks_except_two_158 i j row_ptrs rows
    else
      PtrArray.missing_i x j 0 n row_ptrs **
      row_blocks_except_two_158 i j row_ptrs rows.
