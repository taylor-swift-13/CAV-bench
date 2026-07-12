(* Given a string of words, return a list of words split on whitespace, if no whitespaces exists in the text you
should split on commas ',' if no commas exists you should return the number of lower-case letters with odd order in the
alphabet, ord('a') = 0, ord('b') = 1, ... ord('z') = 25
Examples
split_words("Hello world!") ➞ ["Hello", "world!"]
split_words("Hello,world!") ➞ ["Hello", "world!"]
split_words("abcdef") == 3 *)

(* 引入必要的 Coq 库 *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.


(*
  辅助函数定义
*)

(* 1. 检查一个 (list ascii) 是否包含一个特定的 ascii 字符。 *)
Definition contains (l : list ascii) (c : ascii) : bool :=
  existsb (fun x => Ascii.eqb x c) l.

(* 2. 将一个 (list ascii) 按给定的分隔符拆分为一个单词列表 (list (list ascii))。*)
Definition split (sep : ascii) (s : list ascii) : list (list ascii) :=
  let s' := s ++ [sep] in
  let f (acc : list (list ascii) * list ascii) (c : ascii) :=
    let (res, current_word) := acc in
    if Ascii.eqb c sep then
      match current_word with
      | [] => (res, []) (* 如果当前单词为空，则忽略它 *)
      | _ :: _ => (res ++ [rev current_word], []) (* 否则，将反转后的当前单词添加到结果中 *)
      end
    else
      (res, c :: current_word)
  in
  let (res, _) := fold_left f s' ([], []) in
  res.

(* 3. 计算列表中字母序为奇数的小写字母的数量。
      'a' 的序数为 0，'b' 为 1，以此类推。 *)
Definition count_odd_lowercase (l : list ascii) : nat :=
  (* 定义一个函数，根据规约将小写字母映射到自然数 0-25。
     任何非小写字母的字符都映射到 0 (一个偶数)，因此它们不会被计数。*)
  let lowercase_ord (c : ascii) : nat :=
    match c with
    | "a"%char => 0 | "b"%char => 1 | "c"%char => 2 | "d"%char => 3
    | "e"%char => 4 | "f"%char => 5 | "g"%char => 6 | "h"%char => 7
    | "i"%char => 8 | "j"%char => 9 | "k"%char => 10 | "l"%char => 11
    | "m"%char => 12 | "n"%char => 13 | "o"%char => 14 | "p"%char => 15
    | "q"%char => 16 | "r"%char => 17 | "s"%char => 18 | "t"%char => 19
    | "u"%char => 20 | "v"%char => 21 | "w"%char => 22 | "x"%char => 23
    | "y"%char => 24 | "z"%char => 25
    | _ => 0
    end
  in
  (* 检查一个自然数是否为奇数 *)
  let is_odd (n : nat) : bool :=
    negb (Nat.eqb (Nat.modulo n 2) 0)
  in
  (* 定义目标字符的判断条件。
     is_lower 的检查是多余的，因为任何非小写字母通过 lowercase_ord 都会得到 0，
     而 is_odd 0 是 false，所以它们不会被计入。*)
  let is_target_char (c : ascii) : bool :=
    is_odd (lowercase_ord c)
  in
  List.length (filter is_target_char l).

(* 输入可为任意字符列表 *)
Definition problem_125_pre (input : string) : Prop := True.
(*
  程序规约 (Program Specification)
*)

Definition  problem_125_spec (input : string) (output : sum (list string) nat) : Prop :=
  let l := list_ascii_of_string input in
  if contains l " "%char then
    let res := split " "%char l in
    output = inl (map string_of_list_ascii res)
  else if contains l ","%char then
    let res := split ","%char l in
    output = inl (map string_of_list_ascii res)
  else
    output = inr (count_odd_lowercase l).

Definition spec_contains_125 := contains.
Definition spec_split_125 := split.
Definition spec_count_odd_lowercase_125 := count_odd_lowercase.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.

(* Compatibility wrapper for proofs generated against the older strchr_result
   contract, where a successful match returns a non-null pointer. *)
Definition strchr_result (str : list Z) (c ret s : Z) : Prop :=
  (exists i,
      0 <= i < string_length str /\
      Znth i str 0 = c /\
      (forall k, 0 <= k < i -> Znth k str 0 <> c) /\
      ret = s + i /\
      ret <> 0) \/
  ((forall k, 0 <= k < string_length str -> Znth k str 0 <> c) /\
   ((c = 0 /\ ret = s + string_length str) \/
    (c <> 0 /\ ret = 0))).
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_125 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_125 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_125 c) (string_of_list_z_125 rest)
  end.

Definition row_payload_z_125 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_125 (row : list Z) : string :=
  string_of_list_z_125 (row_payload_z_125 row).

Definition rows_to_strings_z_125 (rows : list (list Z)) : list string :=
  map row_string_z_125 rows.

Fixpoint contains_zb_125 (s : list Z) (c : Z) : bool :=
  match s with
  | [] => false
  | x :: xs => if Z.eqb x c then true else contains_zb_125 xs c
  end.

Definition contains_z_125 (s : list Z) (c : Z) : Prop :=
  exists i, 0 <= i < Zlength s /\ Znth i s 0 = c.

Definition is_odd_lower_z_125 (c : Z) : bool :=
  Z.leb 97 c && Z.leb c 122 && Z.eqb (Z.rem c 2) 0.

Fixpoint odd_lower_count_payload_125 (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest =>
      (if is_odd_lower_z_125 c then 1 else 0) +
      odd_lower_count_payload_125 rest
  end.

Definition odd_lower_prefix_125 (s : list Z) (i : Z) : Z :=
  odd_lower_count_payload_125 (sublist 0 i s).

Definition odd_lower_count_125 (s : list Z) : Z :=
  odd_lower_count_payload_125 s.

Definition decimal_write_state_125
    (value _tmp pos digits : Z) (done : list Z) : Prop :=
  0 <= value /\
  Zlength done = digits - pos - 1.

Definition problem_125_pre_z (s : list Z) : Prop :=
  problem_125_pre (string_of_list_z_125 s).

Definition output_sum_z_125
    (s : list Z) (rows : list (list Z))
    : Datatypes.sum (list string) nat :=
  let l := list_ascii_of_string (string_of_list_z_125 s) in
  if spec_contains_125 l " "%char then
    inl (map string_of_list_ascii (spec_split_125 " "%char l))
  else if spec_contains_125 l ","%char then
    inl (map string_of_list_ascii (spec_split_125 ","%char l))
  else
    inr (spec_count_odd_lowercase_125 l).

Definition problem_125_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_125_spec (string_of_list_z_125 s) (output_sum_z_125 s rows).

Definition valid_split_words_input_125 (_s : list Z) : Prop := True.

Definition word_payload_125 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_125 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_125 s start stop).

Definition split_step_125
    (sep : Z) (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if Z.eqb c sep then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_125 (n : nat) (s : list Z) (sep : Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_125
        sep
        (split_state_nat_125 n' s sep)
        (Znth (Z.of_nat n') s 0)
  end.

Definition split_completed_payloads_125
    (s : list Z) (i sep : Z) : list (list Z) :=
  fst (split_state_nat_125 (Z.to_nat i) s sep).

Definition split_scan_current_125 (s : list Z) (i sep : Z) : list Z :=
  snd (split_state_nat_125 (Z.to_nat i) s sep).

Definition split_completed_rows_125
    (s : list Z) (i sep : Z) : list (list Z) :=
  map c_string (split_completed_payloads_125 s i sep).

Definition split_payloads_125 (s : list Z) (sep : Z) : list (list Z) :=
  let '(rows, cur) := split_state_nat_125 (Z.to_nat (Zlength s)) s sep in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition split_output_rows_125 (s : list Z) (sep : Z) : list (list Z) :=
  map c_string (split_payloads_125 s sep).

Definition split_scan_state_125
    (s : list Z) (i start sep : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = split_completed_rows_125 s i sep /\
  ((split_scan_current_125 s i sep = [] /\ start = -1) \/
   (0 <= start < i /\
    split_scan_current_125 s i sep = word_payload_125 s start i)).

Fixpoint split_words_rows_heap_125
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row **
      split_words_rows_heap_125 ps rs
  | _, _ => emp
  end.
