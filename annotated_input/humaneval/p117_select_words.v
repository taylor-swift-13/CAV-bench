(* Given a string s and a natural number n, you have been tasked to implement
a function that returns a list of all words from string s that contain exactly
n consonants, in order these words appear in the string s.
If the string s is empty then the function should return an empty list.
Note: you may assume the input string contains only letters and spaces.
Examples:
select_words("Mary had a little lamb", 4) ==> ["little"]
select_words("Mary had a little lamb", 3) ==> ["Mary", "lamb"]
select_words("simple white space", 2) ==> []
select_words("Hello world", 4) ==> ["world"]
select_words("Uncle sam", 3) ==> ["Uncle"] *)

Require Import Coq.Strings.Ascii Coq.Strings.String Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char => true | "e"%char => true | "i"%char => true | "o"%char => true | "u"%char => true
  | "A"%char => true | "E"%char => true | "I"%char => true | "O"%char => true | "U"%char => true
  | _ => false
  end.

Definition is_letter (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 65 n) && (Nat.leb n 90)) ||
  ((Nat.leb 97 n) && (Nat.leb n 122)).

Definition is_consonant (c : ascii) : bool :=
  is_letter c && negb (is_vowel c).

Definition count_consonants (w : list ascii) : nat :=
  length (filter is_consonant w).

Definition only_spaces (xs : list ascii) : Prop :=
  Forall (fun c => c = " "%char) xs.

Definition nonempty_spaces (xs : list ascii) : Prop :=
  xs <> [] /\ only_spaces xs.

Definition word_chars (w : list ascii) : Prop :=
  w <> [] /\ Forall (fun c => c <> " "%char) w.

Definition separated_words
    (front : list (list ascii)) (seps : list (list ascii)) (last : list ascii)
    : list ascii :=
  (concat (map (fun ws => ((fst ws) ++ (snd ws))%list) (combine front seps)) ++ last)%list.

Definition split_words_shape (s : list ascii) (words : list (list ascii)) : Prop :=
  (words = [] /\ only_spaces s) \/
  exists leading trailing front last seps,
    words = (front ++ [last])%list /\
    Forall word_chars (front ++ [last]) /\
    only_spaces leading /\
    only_spaces trailing /\
    Forall nonempty_spaces seps /\
    length seps = length front /\
    s = (leading ++ separated_words front seps last ++ trailing)%list.

Definition select_words_impl (words : list (list ascii)) (n : nat) : list (list ascii) :=
  filter (fun w => Nat.eqb (count_consonants w) n) words.

(* 字符串只含字母与空格 *)
Definition problem_117_pre (s : string) : Prop :=
  let l := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122)) l.

Definition problem_117_spec (s : string) (n : nat) (output : list string) : Prop :=
  exists words,
    split_words_shape (list_ascii_of_string s) words /\
    output = map string_of_list_ascii (select_words_impl words n).
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
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition ascii_of_z_117 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_117 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_117 c) (string_of_list_z_117 rest)
  end.

Definition row_payload_z_117 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_117 (row : list Z) : string :=
  string_of_list_z_117 (row_payload_z_117 row).

Definition rows_to_strings_z_117 (rows : list (list Z)) : list string :=
  map row_string_z_117 rows.

Definition problem_117_pre_z (s : list Z) : Prop :=
  problem_117_pre (string_of_list_z_117 s).

Definition problem_117_spec_z (s : list Z) (need : Z) (rows : list (list Z)) : Prop :=
  problem_117_spec (string_of_list_z_117 s) (Z.to_nat need) (rows_to_strings_z_117 rows).

Definition is_space_z_117 (c : Z) : bool :=
  Z.eqb c 32.

Definition is_letter_z_117 (c : Z) : bool :=
  (Z.leb 65 c && Z.leb c 90) || (Z.leb 97 c && Z.leb c 122).

Definition is_vowel_z_117 (c : Z) : bool :=
  Z.eqb c 65 || Z.eqb c 69 || Z.eqb c 73 || Z.eqb c 79 || Z.eqb c 85 ||
  Z.eqb c 97 || Z.eqb c 101 || Z.eqb c 105 || Z.eqb c 111 || Z.eqb c 117.

Definition is_consonant_z_117 (c : Z) : bool :=
  is_letter_z_117 c && negb (is_vowel_z_117 c).

Fixpoint count_consonants_z_117 (w : list Z) : Z :=
  match w with
  | [] => 0
  | c :: rest =>
      (if is_consonant_z_117 c then 1 else 0) + count_consonants_z_117 rest
  end.

Definition valid_select_words_char_117 (c : Z) : Prop :=
  c = 32 \/ (65 <= c <= 90) \/ (97 <= c <= 122).

Definition valid_select_words_input_117 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_select_words_char_117 (Znth i s 0).

Definition word_payload_117 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition word_row_117 (s : list Z) (start stop : Z) : list Z :=
  c_string (word_payload_117 s start stop).

Definition select_step_117
    (need : Z) (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_space_z_117 c then
    match cur with
    | [] => (rows, [])
    | _ =>
        if Z.eqb (count_consonants_z_117 cur) need
        then (rows ++ [cur], [])
        else (rows, [])
    end
  else (rows, cur ++ [c]).

Fixpoint select_state_nat_117 (n : nat) (s : list Z) (need : Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      select_step_117 need
        (select_state_nat_117 n' s need)
        (Znth (Z.of_nat n') s 0)
  end.

Definition select_completed_payloads_117 (s : list Z) (i need : Z)
    : list (list Z) :=
  fst (select_state_nat_117 (Z.to_nat i) s need).

Definition select_current_117 (s : list Z) (i need : Z) : list Z :=
  snd (select_state_nat_117 (Z.to_nat i) s need).

Definition select_completed_rows_117 (s : list Z) (i need : Z)
    : list (list Z) :=
  map c_string (select_completed_payloads_117 s i need).

Definition select_payloads_117 (s : list Z) (need : Z) : list (list Z) :=
  let '(rows, cur) := select_state_nat_117 (Z.to_nat (Zlength s)) s need in
  match cur with
  | [] => rows
  | _ =>
      if Z.eqb (count_consonants_z_117 cur) need
      then rows ++ [cur]
      else rows
  end.

Definition all_step_117
    (st : list (list Z) * list Z) (c : Z)
    : list (list Z) * list Z :=
  let '(rows, cur) := st in
  if is_space_z_117 c then
    match cur with
    | [] => (rows, [])
    | _ => (rows ++ [cur], [])
    end
  else (rows, cur ++ [c]).

Fixpoint all_state_nat_117 (n : nat) (s : list Z)
  : list (list Z) * list Z :=
  match n with
  | O => ([], [])
  | S n' =>
      all_step_117
        (all_state_nat_117 n' s)
        (Znth (Z.of_nat n') s 0)
  end.

Definition all_payloads_117 (s : list Z) : list (list Z) :=
  let '(rows, cur) := all_state_nat_117 (Z.to_nat (Zlength s)) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.

Definition only_spaces_z_117 (xs : list Z) : Prop :=
  Forall (fun c => c = 32) xs.

Definition nonempty_spaces_z_117 (xs : list Z) : Prop :=
  xs <> [] /\ only_spaces_z_117 xs.

Definition word_chars_z_117 (w : list Z) : Prop :=
  w <> [] /\ Forall (fun c => c <> 32) w.

Definition separated_words_z_117
    (front : list (list Z)) (seps : list (list Z)) (last : list Z)
    : list Z :=
  (List.concat (map (fun ws => (fst ws ++ snd ws)%list) (combine front seps)) ++ last)%list.

Definition split_words_shape_z_117 (s : list Z) (words : list (list Z)) : Prop :=
  (words = [] /\ only_spaces_z_117 s) \/
  exists leading trailing front last seps,
    words = (front ++ [last])%list /\
    Forall word_chars_z_117 (front ++ [last])%list /\
    only_spaces_z_117 leading /\
    only_spaces_z_117 trailing /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps last ++ trailing)%list.

Definition closed_shape_z_117 (s : list Z) (rows : list (list Z)) : Prop :=
  (rows = [] /\ only_spaces_z_117 s) \/
  exists leading trailing front last seps,
    rows = (front ++ [last])%list /\
    Forall word_chars_z_117 (front ++ [last])%list /\
    only_spaces_z_117 leading /\
    nonempty_spaces_z_117 trailing /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps last ++ trailing)%list.

Definition open_shape_z_117
    (s : list Z) (rows : list (list Z)) (cur : list Z) : Prop :=
  exists leading front seps,
    rows = front /\
    Forall word_chars_z_117 (front ++ [cur])%list /\
    only_spaces_z_117 leading /\
    Forall nonempty_spaces_z_117 seps /\
    List.length seps = List.length front /\
    s = (leading ++ separated_words_z_117 front seps cur)%list.

Definition state_shape_z_117
    (s : list Z) (rows : list (list Z)) (cur : list Z) : Prop :=
  match cur with
  | [] => closed_shape_z_117 s rows
  | _ => open_shape_z_117 s rows cur
  end.

Definition select_output_rows_117 (s : list Z) (need : Z) : list (list Z) :=
  map c_string (select_payloads_117 s need).

Definition select_scan_state_117
    (s : list Z) (i start numc need : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = select_completed_rows_117 s i need /\
  ((select_current_117 s i need = [] /\ start = -1 /\ numc = 0) \/
   (0 <= start < i /\
    select_current_117 s i need = word_payload_117 s start i /\
    numc = count_consonants_z_117 (word_payload_117 s start i))).

Fixpoint select_words_rows_heap_117
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** select_words_rows_heap_117 ps rs
  | _, _ => emp
  end.

Definition ascii_range_z_117 (z : Z) : Prop := 0 <= z <= 127.

Definition ascii_range_list_117 (xs : list Z) : Prop :=
  Forall ascii_range_z_117 xs.
