(*  Filter an input list of strings only for ones that contain given substring
>>> filter_by_substring([], 'a')
[]
>>> filter_by_substring(['abc', 'bacd', 'cde', 'array'], 'a')
['abc', 'bacd', 'array']
 *)

(* ∀str, In(str, output) ↔ (In(str, strings) ∧ Contains(str, s))
  ∀i j ∈ [0,length(output)), ∃k l ∈ [0,length(intput)), input[k] = output[i] /\ input[l] = output[j] -> i < j -> k < l
  *)

Require Import List.
Require Import String.
Import ListNotations.

Open Scope string_scope.


(* 判断 s 是否包含子串 sub *)
Fixpoint contains_substring (s sub : string) : bool :=
  match s with
  | EmptyString => if sub =? EmptyString then true else false
  | String _ rest =>
      if String.prefix sub s then true
      else contains_substring rest sub
  end.

Fixpoint filter_by_substring_impl (input : list string) (sub : string) : list string :=
  match input with
  | [] => []
  | h :: t =>
    if contains_substring h sub then
      h :: filter_by_substring_impl t sub
    else
      filter_by_substring_impl t sub
  end.

Definition problem_7_pre : Prop:= True.

Definition problem_7_spec (input output : list string) (sub : string) : Prop :=
  output = filter_by_substring_impl input sub.
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


(* Case-local compatibility with the source proof; DLC intentionally keeps the
   benchmark's pinned string library unchanged. *)
Definition substring_at (str sub : list Z) (i : Z) : Prop :=
  0 <= i <= string_length str /\
  i + string_length sub <= string_length str /\
  forall k, 0 <= k < string_length sub ->
    Znth (i + k) str 0 = Znth k sub 0.

Definition strstr_result (str sub : list Z) (ret s : Z) : Prop :=
  (exists i,
      substring_at str sub i /\
      (forall k, 0 <= k < i -> ~ substring_at str sub k) /\
      ret = s + i /\
      ret <> 0) \/
  ((forall k, 0 <= k <= string_length str -> ~ substring_at str sub k) /\
   ret = 0).
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition ascii_of_z_7 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_7 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_7 c) (string_of_list_z_7 rest)
  end.

Definition row_payload_z_7 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_7 (row : list Z) : string :=
  string_of_list_z_7 (row_payload_z_7 row).

Definition rows_to_strings_z_7 (rows : list (list Z)) : list string :=
  map row_string_z_7 rows.

Definition rows_well_formed_7 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_7 row in
    row = c_string payload /\
    valid_string payload /\
    string_length payload < INT_MAX.

Definition problem_7_pre_z (rows : list (list Z)) : Prop :=
  problem_7_pre.

Definition problem_7_spec_z
    (rows : list (list Z)) (substring : list Z) (output_rows : list (list Z)) : Prop :=
  problem_7_spec
    (rows_to_strings_z_7 rows)
    (rows_to_strings_z_7 output_rows)
    (string_of_list_z_7 substring).

Definition substring_match_z_7 (row : list Z) (substring : list Z) : Prop :=
  contains_substring (row_string_z_7 row) (string_of_list_z_7 substring) = true.

Fixpoint filter_substring_rows_7
    (rows : list (list Z)) (substring : list Z) : list (list Z) :=
  match rows with
  | [] => []
  | row :: rest =>
      if contains_substring (row_string_z_7 row) (string_of_list_z_7 substring)
      then row :: filter_substring_rows_7 rest substring
      else filter_substring_rows_7 rest substring
  end.

Definition filter_substring_prefix_7
    (rows : list (list Z)) (substring : list Z) (k : Z) : list (list Z) :=
  filter_substring_rows_7 (firstn (Z.to_nat k) rows) substring.

Definition filter_substring_state_7
    (rows : list (list Z)) (substring : list Z) (k : Z)
    (output_rows : list (list Z)) : Prop :=
  0 <= k <= Zlength rows /\
  output_rows = filter_substring_prefix_7 rows substring k.
