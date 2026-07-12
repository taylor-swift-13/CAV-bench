(* You will be given a string of words separated by commas or spaces. Your task is
to split the string into words and return an array of the words.

For example:
words_string("Hi, my name is John") == ["Hi", "my", "name", "is", "John"]
words_string("One, two, three, four, five, six") == ["One", "two", "three", "four", "five", "six"] *)

Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.



Definition is_delimiter (c : ascii) : bool :=
  match c with
  | ","%char | " "%char => true | _ => false end.

Fixpoint words_string_aux (current_word : list ascii) (input : list ascii) : list (list ascii) :=
  match input with
  | [] => match current_word with [] => [] | _ => [current_word] end
  | c :: cs => if is_delimiter c then
                 match current_word with
                 | [] => words_string_aux [] cs
                 | _ => current_word :: words_string_aux [] cs
                 end
               else words_string_aux (current_word ++ [c]) cs
  end.

Definition words_string_list_impl (s : list ascii) : list (list ascii) :=
  words_string_aux [] s.

Definition words_string (s : string) : list string :=
  map string_of_list_ascii (words_string_list_impl (list_ascii_of_string s)).

(* 输入为仅包含字母、逗号或空格的字符列表 *)
Definition problem_101_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c =>
    let n := nat_of_ascii c in
      (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ c = ","%char \/ c = " "%char) l.

Definition problem_101_spec (s : string) (output : list string) : Prop :=
  output = words_string s.
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
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_101 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_101 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_101 c) (string_of_list_z_101 rest)
  end.

Definition row_payload_z_101 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_101 (row : list Z) : string :=
  string_of_list_z_101 (row_payload_z_101 row).

Definition rows_to_strings_z_101 (rows : list (list Z)) : list string :=
  map row_string_z_101 rows.

Definition problem_101_pre_z (s : list Z) : Prop :=
  problem_101_pre (string_of_list_z_101 s).

Definition problem_101_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_101_spec (string_of_list_z_101 s) (rows_to_strings_z_101 rows).

Definition is_delim_z_101 (c : Z) : bool :=
  Z.eqb c 32 || Z.eqb c 44.

Definition valid_words_char_101 (c : Z) : Prop :=
  c = 32 \/ c = 44 \/ (65 <= c <= 90) \/ (97 <= c <= 122).

Definition valid_words_input_101 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_words_char_101 (Znth i s 0).

Definition word_payload_101 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_101 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_101 s start stop).

Definition split_step_101
    (st : list (list Z) * list Z) (c : Z) : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_delim_z_101 c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_101 (n : nat) (s : list Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_101
        (split_state_nat_101 n' s)
        (Znth (Z.of_nat n') s 0)
  end.

Definition split_completed_payloads_101 (s : list Z) (i : Z) : list (list Z) :=
  fst (split_state_nat_101 (Z.to_nat i) s).

Definition split_scan_current_101 (s : list Z) (i : Z) : list Z :=
  snd (split_state_nat_101 (Z.to_nat i) s).

Definition split_completed_rows_101 (s : list Z) (i : Z) : list (list Z) :=
  map c_string (split_completed_payloads_101 s i).

Definition words_payloads_101 (s : list Z) : list (list Z) :=
  let '(rows, cur) := split_state_nat_101 (Z.to_nat (Zlength s)) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition words_output_rows_101 (s : list Z) : list (list Z) :=
  map c_string (words_payloads_101 s).

Definition split_scan_state_101
    (s : list Z) (i start : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = split_completed_rows_101 s i /\
  ((split_scan_current_101 s i = [] /\ start = -1) \/
   (0 <= start < i /\ split_scan_current_101 s i = word_payload_101 s start i)).

Fixpoint words_rows_heap_101
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** words_rows_heap_101 ps rs
  | _, _ => emp
  end.

Definition split_step_ascii_101
    (st : list (list ascii) * list ascii) (c : ascii)
    : list (list ascii) * list ascii :=
  let '(rows, cur) := st in
  if is_delimiter c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint split_state_nat_ascii_101 (n : nat) (s : list ascii)
  : list (list ascii) * list ascii :=
  match n with
  | O => ([], [])
  | S n' =>
      split_step_ascii_101
        (split_state_nat_ascii_101 n' s)
        (nth n' s "000"%char)
  end.

Definition split_state_list_ascii_101
    (s : list ascii) (st : list (list ascii) * list ascii)
    : list (list ascii) * list ascii :=
  fold_left (fun acc c => split_step_ascii_101 acc c) s st.

Definition map_state_ascii_101
    (st : list (list Z) * list Z) : list (list ascii) * list ascii :=
  (map (map ascii_of_z_101) (fst st), map ascii_of_z_101 (snd st)).
