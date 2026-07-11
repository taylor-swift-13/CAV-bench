(* Given a list of strings, where each string consists of only digits, return a list.
Each element i of the output should be "the number of odd elements in the
string i of the input." where all the i's should be replaced by the number
of odd digits in the i'th string of the input.

>>> odd_count(['1234567'])
["the number of odd elements 4n the str4ng 4 of the 4nput."]
>>> odd_count(['3',"11111111"])
["the number of odd elements 1n the str1ng 1 of the 1nput.",
"the number of odd elements 8n the str8ng 8 of the 8nput."] *)

Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii.
Require Import Coq.NArith.NArith Coq.Numbers.DecimalString.
Import ListNotations.

Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Definition count_odd_digits (s : string) : nat :=
  List.length (List.filter is_odd_digit (list_ascii_of_string s)).

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (N.to_uint (N.of_nat n)).

Definition replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  string_of_list_ascii
    (List.flat_map
       (fun c =>
          if Ascii.eqb c target
          then list_ascii_of_string replacement
          else [c])
       (list_ascii_of_string s)).

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

(* 每个字符串只包含数字字符 *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    Forall (fun ch =>
      let n := nat_of_ascii ch in 48 <= n /\ n <= 57)
      (list_ascii_of_string s)) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.
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

Parameter LitMap : string -> addr.

Definition nil_z_113 : list Z := nil.

Definition row_at_113 (i : Z) (rows : list (list Z)) : list Z :=
  Znth i rows nil_z_113.

Definition ascii_of_z_113 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_113 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_113 c) (string_of_list_z_113 rest)
  end.

Definition row_payload_z_113 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_113 (row : list Z) : string :=
  string_of_list_z_113 (row_payload_z_113 row).

Definition rows_to_strings_z_113 (rows : list (list Z)) : list string :=
  map row_string_z_113 rows.

Definition problem_113_pre_z (rows : list (list Z)) : Prop :=
  problem_113_pre (rows_to_strings_z_113 rows).

Definition problem_113_spec_z
    (rows output_rows : list (list Z)) : Prop :=
  problem_113_spec
    (rows_to_strings_z_113 rows)
    (rows_to_strings_z_113 output_rows).

Definition rows_well_formed_113 (rows : list (list Z)) (n : Z) : Prop :=
  Zlength rows = n /\
  forall k,
    0 <= k < n ->
    let row := Znth k rows nil in
    let payload := row_payload_z_113 row in
    row = c_string payload /\
    valid_string payload /\
    all_ascii payload /\
    string_length payload < INT_MAX.

Definition is_odd_digit_z_113 (c : Z) : bool :=
  Z.eqb c 49 || Z.eqb c 51 || Z.eqb c 53 || Z.eqb c 55 || Z.eqb c 57.

Fixpoint count_odd_digits_payload_113 (s : list Z) : Z :=
  match s with
  | [] => 0
  | c :: rest =>
      (if is_odd_digit_z_113 c then 1 else 0) +
      count_odd_digits_payload_113 rest
  end.

Definition odd_digit_count_prefix_113 (s : list Z) (i : Z) : Z :=
  count_odd_digits_payload_113 (sublist 0 i s).

Definition odd_digit_count_row_113 (row : list Z) : Z :=
  count_odd_digits_payload_113 (row_payload_z_113 row).

Fixpoint uint_digits_z_113 (d : Decimal.uint) : list Z :=
  match d with
  | Decimal.Nil => []
  | Decimal.D0 rest => 48 :: uint_digits_z_113 rest
  | Decimal.D1 rest => 49 :: uint_digits_z_113 rest
  | Decimal.D2 rest => 50 :: uint_digits_z_113 rest
  | Decimal.D3 rest => 51 :: uint_digits_z_113 rest
  | Decimal.D4 rest => 52 :: uint_digits_z_113 rest
  | Decimal.D5 rest => 53 :: uint_digits_z_113 rest
  | Decimal.D6 rest => 54 :: uint_digits_z_113 rest
  | Decimal.D7 rest => 55 :: uint_digits_z_113 rest
  | Decimal.D8 rest => 56 :: uint_digits_z_113 rest
  | Decimal.D9 rest => 57 :: uint_digits_z_113 rest
  end.

Definition decimal_digits_113 (n : Z) : list Z :=
  match N.to_uint (N.of_nat (Z.to_nat n)) with
  | Decimal.Nil => [48]
  | d => uint_digits_z_113 d
  end.

Definition template_payload_113 : list Z :=
  [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
   111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32; 105;
   110; 32; 116; 104; 101; 32; 115; 116; 114; 105; 110; 103; 32; 105;
   32; 111; 102; 32; 116; 104; 101; 32; 105; 110; 112; 117; 116; 46].

Definition template_literal_113 : string :=
  "the number of odd elements in the string i of the input."%string.

Definition template_len_113 : Z := Zlength template_payload_113.

Fixpoint replace_i_payload_113 (tmpl digits : list Z) : list Z :=
  match tmpl with
  | [] => []
  | c :: rest =>
      if Z.eqb c 105
      then digits ++ replace_i_payload_113 rest digits
      else c :: replace_i_payload_113 rest digits
  end.

Fixpoint count_i_payload_113 (tmpl : list Z) : Z :=
  match tmpl with
  | [] => 0
  | c :: rest =>
      (if Z.eqb c 105 then 1 else 0) + count_i_payload_113 rest
  end.

Definition template_prefix_payload_113 (i : Z) (digits : list Z) : list Z :=
  replace_i_payload_113 (firstn (Z.to_nat i) template_payload_113) digits.

Definition template_fill_state_113
    (i : Z) (digits : list Z) (k : Z) (out_l : list Z) : Prop :=
  0 <= i <= template_len_113 /\
  out_l = template_prefix_payload_113 i digits /\
  k = Zlength out_l.

Definition odd_count_row_113 (row : list Z) : list Z :=
  c_string
    (replace_i_payload_113
       template_payload_113
       (decimal_digits_113 (odd_digit_count_row_113 row))).

Definition odd_count_rows_113 (rows : list (list Z)) : list (list Z) :=
  map odd_count_row_113 rows.

Definition odd_count_state_113
    (rows : list (list Z)) (i : Z) (output_rows : list (list Z)) : Prop :=
  0 <= i <= Zlength rows /\
  output_rows = odd_count_rows_113 (firstn (Z.to_nat i) rows).

Fixpoint odd_count_rows_heap_113
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** odd_count_rows_heap_113 ps rs
  | _, _ => emp
  end.

Definition template_expanded_113 (digits : list Z) : list Z :=
  [116; 104; 101; 32; 110; 117; 109; 98; 101; 114; 32; 111; 102; 32;
   111; 100; 100; 32; 101; 108; 101; 109; 101; 110; 116; 115; 32] ++
  digits ++
  [110; 32; 116; 104; 101; 32; 115; 116; 114] ++
  digits ++
  [110; 103; 32] ++
  digits ++
  [32; 111; 102; 32; 116; 104; 101; 32] ++
  digits ++
  [110; 112; 117; 116; 46].

Definition template_expanded_ascii_113 (digits : list Z) : list ascii :=
  list_ascii_of_string "the number of odd elements " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "n the str" ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "ng " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string " of the " ++
  map ascii_of_z_113 digits ++
  list_ascii_of_string "nput.".
