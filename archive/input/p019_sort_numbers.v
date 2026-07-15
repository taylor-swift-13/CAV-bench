(* """ Input is a space-delimited string of numberals from 'zero' to 'nine'.
Valid choices are 'zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven', 'eight' and 'nine'.
Return the string with numbers sorted from smallest to largest
>>> sort_numbers('three one five')
'one three five'
""" *)

(* Spec(input, output) :=

∃ input_list, output_list,
    String.concat " " input_list = input ∧
    String.concat " " output_list = output ∧
    IsPermutation(input_list, output_list) ∧
    IsSorted(output_list) *)


(* 导入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Permutation.

(* 导入列表表示法 *)
Import ListNotations.
Open Scope string_scope.

(*
  定义一个从单词 (string) 到数字 (nat) 的关系。
*)
Inductive WordToNum : string -> nat -> Prop :=
  | wtn_zero  : WordToNum "zero" 0
  | wtn_one   : WordToNum "one" 1
  | wtn_two   : WordToNum "two" 2
  | wtn_three : WordToNum "three" 3
  | wtn_four  : WordToNum "four" 4
  | wtn_five  : WordToNum "five" 5
  | wtn_six   : WordToNum "six" 6
  | wtn_seven : WordToNum "seven" 7
  | wtn_eight : WordToNum "eight" 8
  | wtn_nine  : WordToNum "nine" 9.

(* 定义一个谓词，用于判断一个 string 是否是有效的数字单词 *)
Definition is_valid_word (s : string) : Prop :=
  exists n, WordToNum s n.

(*
  定义一个谓词，用于判断一个 string 列表是否已排序。
*)
Definition IsSorted (l : list string) : Prop :=
  forall i j, (i < j)%nat -> j < length l ->
    forall s_i s_j n_i n_j,
      nth i l "" = s_i ->
      nth j l "" = s_j ->
      WordToNum s_i n_i ->
      WordToNum s_j n_j ->
      (n_i <= n_j)%nat.

Definition SpaceDelimited (s : string) (words : list string) : Prop :=
  String.concat " " words = s.

Definition problem_19_pre (input : string) : Prop :=
  exists input_list,
    SpaceDelimited input input_list /\
    Forall is_valid_word input_list.

Definition problem_19_spec (input output : string) : Prop :=
    exists input_list output_list,
    SpaceDelimited input input_list /\
    SpaceDelimited output output_list /\
    Forall is_valid_word input_list /\
    Forall is_valid_word output_list /\

    (*  输出列表是输入列表的一个排列 *)
    Permutation input_list output_list /\

    (*  输出列表是排好序的 *)
    IsSorted output_list.

(* QCP 2.0.4 definition-only annotation interface. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
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

Definition ascii_of_z_19 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_19 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_19 c) (string_of_list_z_19 rest)
  end.

Definition ptr_mixed_store (p lo : Z) (a : option Z) : Assertion :=
  match a with
  | Some v => ((p + lo * sizeof(PTR)) # Ptr |-> v)
  | None => ((p + lo * sizeof(PTR)) # Ptr |->_)
  end.

Fixpoint ptr_mixed_seg (p lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => coq_prop (hi = lo) && emp
  | cons a l' => ptr_mixed_store p lo a ** ptr_mixed_seg p (lo + 1) hi l'
  end.

Fixpoint ptr_mixed_missing_i (p i lo hi : Z) (l : list (option Z)) : Assertion :=
  match l with
  | nil => coq_prop False && emp
  | cons a l' =>
      if Z.eq_dec i lo then ptr_mixed_seg p (lo + 1) hi l'
      else ptr_mixed_store p lo a ** ptr_mixed_missing_i p i (lo + 1) hi l'
  end.

Definition problem_19_pre_z (input : list Z) : Prop :=
  problem_19_pre (string_of_list_z_19 input).

Definition problem_19_spec_z (input output : list Z) : Prop :=
  problem_19_spec (string_of_list_z_19 input) (string_of_list_z_19 output).

Definition ascii_range_z (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127.

Definition SingleSome {A : Type} (l : list (option A)) (n : Z) (a : A) : Prop :=
  l = replace_Znth n (Some a) (repeat None 10).

Definition number_word_z (digit : Z) : list Z :=
  match digit with
  | 0 => [122; 101; 114; 111]
  | 1 => [111; 110; 101]
  | 2 => [116; 119; 111]
  | 3 => [116; 104; 114; 101; 101]
  | 4 => [102; 111; 117; 114]
  | 5 => [102; 105; 118; 101]
  | 6 => [115; 105; 120]
  | 7 => [115; 101; 118; 101; 110]
  | 8 => [101; 105; 103; 104; 116]
  | 9 => [110; 105; 110; 101]
  | 10 => [32]
  | _ => []
  end.

Definition number_word_len_z (digit : Z) : Z :=
  Zlength (number_word_z digit).

Ltac destruct_digit_cases_19 d :=
  let Hcases := fresh "Hcases" in
  assert (Hcases:
    d = 0 \/ d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
    d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) by lia;
  destruct Hcases as [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]];
  subst d.



Definition number_word_ptrs_z
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : list Z :=
  [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9].

Definition number_word_char_full_z (w digit : Z) : Assertion :=
  CharArray.full w (number_word_len_z digit + 1)
    (number_word_z digit ++ [0]).

Definition number_words_chars_full_z
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  number_word_char_full_z w9 9 **
  number_word_char_full_z w8 8 **
  number_word_char_full_z w7 7 **
  number_word_char_full_z w6 6 **
  number_word_char_full_z w5 5 **
  number_word_char_full_z w4 4 **
  number_word_char_full_z w3 3 **
  number_word_char_full_z w2 2 **
  number_word_char_full_z w1 1 **
  number_word_char_full_z w0 0.

Definition number_words_chars_missing_z
  (d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  match d with
  | 0 =>
      coq_prop (word = w0) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1
  | 1 =>
      coq_prop (word = w1) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w0 0
  | 2 =>
      coq_prop (word = w2) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 3 =>
      coq_prop (word = w3) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 4 =>
      coq_prop (word = w4) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 5 =>
      coq_prop (word = w5) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 6 =>
      coq_prop (word = w6) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 7 =>
      coq_prop (word = w7) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w8 8 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 8 =>
      coq_prop (word = w8) &&
      number_word_char_full_z w9 9 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | 9 =>
      coq_prop (word = w9) &&
      number_word_char_full_z w8 8 **
      number_word_char_full_z w7 7 **
      number_word_char_full_z w6 6 **
      number_word_char_full_z w5 5 **
      number_word_char_full_z w4 4 **
      number_word_char_full_z w3 3 **
      number_word_char_full_z w2 2 **
      number_word_char_full_z w1 1 **
      number_word_char_full_z w0 0
  | _ => coq_prop False && emp
  end.

Definition number_words_full
  (words w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  number_words_chars_full_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 **
  PtrArray.full words 10 (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9).

Definition number_words_missing
  (words d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 : Z) : Assertion :=
  PtrArray.missing_i words d 0 10
    (number_word_ptrs_z w0 w1 w2 w3 w4 w5 w6 w7 w8 w9) **
  number_words_chars_missing_z d word w0 w1 w2 w3 w4 w5 w6 w7 w8 w9.

Definition scan_char_z (i : Z) (input : list Z) : Z :=
  if Z.ltb i (Zlength input) then Znth i input 0 else 32.

Fixpoint scan_word_start_nat (fuel : nat) (input : list Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' =>
      let prev := scan_word_start_nat fuel' input in
      let pos := Z.of_nat fuel' in
      if Z.eqb (scan_char_z pos input) 32 then pos + 1 else prev
  end.

Definition scan_word_start_z (i : Z) (input : list Z) : Z :=
  scan_word_start_nat (Z.to_nat i) input.

Definition token_prefix_z (i tlen : Z) (input : list Z) : list Z :=
  if Z.ltb tlen 31 then sublist (i - tlen) i input
  else
    let start := scan_word_start_z i input in
    sublist start (start + tlen) input.

Definition token_unsat_end_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 \/ scan_word_start_z i input + tlen = i.

Definition token_sat_start_z (i tlen : Z) (input : list Z) : Prop :=
  31 <= tlen -> scan_word_start_z i input + 31 <= i.

Definition token_empty_start_z (i tlen : Z) (input : list Z) : Prop :=
  tlen = 0 -> scan_word_start_z i input = i \/ i >= Zlength input.

Definition token_miss_prefix_z (d : Z) (token : list Z) : Prop :=
  forall k, 0 <= k < d -> token <> number_word_z k.

Definition number_word_string (digit : Z) : string :=
  string_of_list_z_19 (number_word_z digit).

Fixpoint SplitOnSpaces_aux_19 (current_group : list ascii) (s : string) : list string :=
  match s with
  | EmptyString =>
      match current_group with
      | [] => []
      | _ => [string_of_list_ascii (List.rev current_group)]
      end
  | String h t =>
      if ascii_dec h " "%char then
        match current_group with
        | [] => SplitOnSpaces_aux_19 [] t
        | _ => string_of_list_ascii (List.rev current_group) :: SplitOnSpaces_aux_19 [] t
        end
      else SplitOnSpaces_aux_19 (h :: current_group) t
  end.

Definition SplitOnSpaces_19 (s : string) : list string :=
  SplitOnSpaces_aux_19 [] s.

Fixpoint SplitOnSpacesZ_aux_19 (current_group : list Z) (input : list Z)
  : list (list Z) :=
  match input with
  | [] =>
      match current_group with
      | [] => []
      | _ => [List.rev current_group]
      end
  | h :: t =>
      if Z.eqb h 32 then
        match current_group with
        | [] => SplitOnSpacesZ_aux_19 [] t
        | _ => List.rev current_group :: SplitOnSpacesZ_aux_19 [] t
        end
      else SplitOnSpacesZ_aux_19 (h :: current_group) t
  end.

Definition SplitOnSpacesZ_19 (input : list Z) : list (list Z) :=
  SplitOnSpacesZ_aux_19 [] input.

Definition list_Z_eq_dec_19 : forall x y : list Z, {x = y} + {x <> y} :=
  list_eq_dec Z.eq_dec.

Definition no_space_z_list_19 (l : list Z) : Prop :=
  forall x, In x l -> x <> 32.




Definition append_number_word_z (prefix : list Z) (digit : Z) : list Z :=
  prefix ++ (if Z.eqb (Zlength prefix) 0 then [] else [32]) ++ number_word_z digit.

Fixpoint append_repeated_number_word_nat
  (prefix : list Z) (digit : Z) (n : nat) : list Z :=
  match n with
  | O => prefix
  | S n' => append_number_word_z
              (append_repeated_number_word_nat prefix digit n') digit
  end.

Definition append_repeated_number_word_z
  (prefix : list Z) (digit count done : Z) : list Z :=
  append_repeated_number_word_nat prefix digit (Z.to_nat done).

Definition sorted_numbers_output_by_counts_z
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : list Z :=
  append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z
    (append_repeated_number_word_z [] 0 c0 c0)
      1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4)
      5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 c8) 9 c9 c9.

Definition output_prefix_z
  (digit done c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : list Z :=
  match digit with
  | 0 => append_repeated_number_word_z [] 0 c0 done
  | 1 => append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 done
  | 2 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 done
  | 3 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 done
  | 4 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 done
  | 5 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 done
  | 6 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 done
  | 7 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 done
  | 8 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 done
  | 9 => append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z
           (append_repeated_number_word_z [] 0 c0 c0) 1 c1 c1) 2 c2 c2) 3 c3 c3) 4 c4 c4) 5 c5 c5) 6 c6 c6) 7 c7 c7) 8 c8 c8) 9 c9 done
  | _ => sorted_numbers_output_by_counts_z c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  end.

Definition output_capacity_prefix_z
  (digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Z :=
  match digit with
  | 0 => 1
  | 1 => 1 + c0 * (number_word_len_z 0 + 1)
  | 2 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1)
  | 3 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1)
  | 4 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1)
  | 5 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1)
  | 6 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1)
  | 7 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1)
  | 8 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1)
  | 9 => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1) + c8 * (number_word_len_z 8 + 1)
  | _ => 1 + c0 * (number_word_len_z 0 + 1) + c1 * (number_word_len_z 1 + 1) + c2 * (number_word_len_z 2 + 1) + c3 * (number_word_len_z 3 + 1) + c4 * (number_word_len_z 4 + 1) + c5 * (number_word_len_z 5 + 1) + c6 * (number_word_len_z 6 + 1) + c7 * (number_word_len_z 7 + 1) + c8 * (number_word_len_z 8 + 1) + c9 * (number_word_len_z 9 + 1)
  end.

Definition count_word_in_string (digit : Z) (input : list Z) : Z :=
  Z.of_nat
    (count_occ list_Z_eq_dec_19
       (SplitOnSpacesZ_19 input)
       (number_word_z digit)).

Definition split_boundary_z (prefix : list Z) : Prop :=
  prefix = [] \/ exists pre, prefix = pre ++ [32].








Definition output_prefix_by_input_z
  (digit done : Z) (input : list Z) : list Z :=
  output_prefix_z digit done
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition output_capacity_prefix_by_input_z
  (digit : Z) (input : list Z) : Z :=
  output_capacity_prefix_z digit
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition output_used_capacity_prefix_z
  (digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Z :=
  let over :=
    output_capacity_prefix_z digit c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 in
  if Z.leb over 1 then 1 else over - 1.

Definition output_used_capacity_prefix_by_input_z
  (digit : Z) (input : list Z) : Z :=
  output_used_capacity_prefix_z digit
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition sorted_numbers_output_z (input : list Z) : list Z :=
  sorted_numbers_output_by_counts_z
    (count_word_in_string 0 input)
    (count_word_in_string 1 input)
    (count_word_in_string 2 input)
    (count_word_in_string 3 input)
    (count_word_in_string 4 input)
    (count_word_in_string 5 input)
    (count_word_in_string 6 input)
    (count_word_in_string 7 input)
    (count_word_in_string 8 input)
    (count_word_in_string 9 input).

Definition number_words_safe_z (input : list Z) : Prop :=
  problem_19_pre_z input /\ ascii_range_z input.

Fixpoint next_word_end_nat (fuel : nat) (pos : Z) (input : list Z) : Z :=
  match fuel with
  | O => pos
  | S fuel' =>
      if Z.geb pos (Zlength input) then pos
      else if Z.eqb (Znth pos input 0) 32 then pos
      else next_word_end_nat fuel' (pos + 1) input
  end.

Definition next_word_end_z (pos : Z) (input : list Z) : Z :=
  next_word_end_nat (Z.to_nat (Zlength input - pos + 1)) pos input.

Definition number_word_digit_at_z (pos : Z) (input : list Z) : Z :=
  let c0 := Znth pos input 0 in
  let c1 := Znth (pos + 1) input 0 in
  if Z.eqb c0 122 then 0
  else if Z.eqb c0 111 then 1
  else if Z.eqb c0 101 then 8
  else if Z.eqb c0 110 then 9
  else if Z.eqb c0 116 then if Z.eqb c1 119 then 2 else 3
  else if Z.eqb c0 102 then if Z.eqb c1 111 then 4 else 5
  else if Z.eqb c1 105 then 6 else 7.

Definition count_update_z (old matched digit : Z) : Z :=
  if Z.eqb matched digit then old + 1 else old.

Definition scan_counts_capacity_z
  (i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  1
  + c0 * (number_word_len_z 0 + 1)
  + c1 * (number_word_len_z 1 + 1)
  + c2 * (number_word_len_z 2 + 1)
  + c3 * (number_word_len_z 3 + 1)
  + c4 * (number_word_len_z 4 + 1)
  + c5 * (number_word_len_z 5 + 1)
  + c6 * (number_word_len_z 6 + 1)
  + c7 * (number_word_len_z 7 + 1)
  + c8 * (number_word_len_z 8 + 1)
  + c9 * (number_word_len_z 9 + 1) <= 1 + 6 * i.

Definition scan_completed_prefix_z (i tlen : Z) (input : list Z) : list Z :=
  if Z.ltb tlen 31 then
    sublist 0 (Z.min (i - tlen) (Zlength input)) input
  else
    sublist 0 (Z.min (scan_word_start_z i input) (Zlength input)) input.

Definition scan_counts_exact_z
  (i tlen : Z) (input : list Z)
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  c0 = count_word_in_string 0 (scan_completed_prefix_z i tlen input) /\
  c1 = count_word_in_string 1 (scan_completed_prefix_z i tlen input) /\
  c2 = count_word_in_string 2 (scan_completed_prefix_z i tlen input) /\
  c3 = count_word_in_string 3 (scan_completed_prefix_z i tlen input) /\
  c4 = count_word_in_string 4 (scan_completed_prefix_z i tlen input) /\
  c5 = count_word_in_string 5 (scan_completed_prefix_z i tlen input) /\
  c6 = count_word_in_string 6 (scan_completed_prefix_z i tlen input) /\
  c7 = count_word_in_string 7 (scan_completed_prefix_z i tlen input) /\
  c8 = count_word_in_string 8 (scan_completed_prefix_z i tlen input) /\
  c9 = count_word_in_string 9 (scan_completed_prefix_z i tlen input).

Definition scan_counts_z
  (i : Z) (input : list Z)
  (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Z) : Prop :=
  0 <= i <= Zlength input + 1 /\
  0 <= c0 <= i /\ 0 <= c1 <= i /\
  0 <= c2 <= i /\ 0 <= c3 <= i /\
  0 <= c4 <= i /\ 0 <= c5 <= i /\
  0 <= c6 <= i /\ 0 <= c7 <= i /\
  0 <= c8 <= i /\ 0 <= c9 <= i /\
  scan_counts_capacity_z i c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.
