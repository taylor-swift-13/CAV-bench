(*Input to this function is a string containing multiple groups of nested parentheses. Your goal is to
separate those group into separate strings and return the list of those.
Separate groups are balanced (each open brace is properly closed) and not nested within each other
Ignore any spaces in the input string.
>>> separate_paren_groups('( ) (( )) (( )( ))')
['()', '(())', '(()())'] *)

(* 引入所需的基础库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义 '(' 和 ')' 的 ASCII 表示 *)
Definition lparen : ascii := "(".
Definition rparen : ascii := ")".
Definition space : ascii := " ".

(*
  规约 1: balanced_chars(cs)
  使用前缀计数关系刻画括号平衡，避免在规格文件中写本地递归定义。
*)
Definition balanced_chars (cs : list ascii) : Prop :=
  count_occ ascii_dec cs lparen = count_occ ascii_dec cs rparen /\
  forall prefix suffix,
    cs = (prefix ++ suffix)%list ->
    count_occ ascii_dec prefix rparen <= count_occ ascii_dec prefix lparen.

Definition IsBalanced (s : string) : Prop :=
  balanced_chars (list_ascii_of_string s).

(*
  辅助函数: 移除列表中的空格。这里复用标准库 filter，而非本地递归。
*)
Definition nonspace_char (c : ascii) : bool :=
  if ascii_dec c space then false else true.

Definition chars_without_spaces (s : string) : list ascii :=
  filter nonspace_char (list_ascii_of_string s).

Definition remove_spaces (s : string) : string :=
  string_of_list_ascii (chars_without_spaces s).

(*
  辅助断言: 检查一个字符是否为括号或空格
  直接使用等式，其类型为 Prop
*)
Definition is_paren_or_space (c : ascii) : Prop :=
  c = lparen \/ c = rparen \/ c = space.

(*
  辅助断言: 字符是否为括号。
*)
Definition is_paren (c : ascii) : Prop :=
  c = lparen \/ c = rparen.

(*
  辅助断言: 检查字符串中的所有字符是否满足属性 P。
  这里复用标准库 List.Forall。
*)
Definition ForallChars (P : ascii -> Prop) (s : string) : Prop :=
  Forall P (list_ascii_of_string s).

(*
  一个 primitive group 是一个非空、平衡、只含括号的最外层括号组；
  “没有非空真前缀已经平衡”排除了 "()()" 这类多个组粘在一起的情况。
*)
Definition primitive_group_chars (cs : list ascii) : Prop :=
  cs <> [] /\
  Forall is_paren cs /\
  balanced_chars cs /\
  forall prefix suffix,
    cs = (prefix ++ suffix)%list ->
    prefix <> [] ->
    suffix <> [] ->
    ~ balanced_chars prefix.

Definition primitive_group (s : string) : Prop :=
  primitive_group_chars (list_ascii_of_string s).

Definition output_chars (output : list string) : list ascii :=
  List.concat (map list_ascii_of_string output).

(*
  前提条件: separate_paren_groups_pre
  1. 输入列表中的所有字符都必须是括号或空格。
  2. 移除空格后的输入列表必须是平衡的。
*)
Definition problem_1_pre (input : string) : Prop :=
  (ForallChars is_paren_or_space input) /\
  (balanced_chars (chars_without_spaces input)).
(*
  最终的程序规约: separate_paren_groups_spec(input, output)
*)
Definition problem_1_spec (input : string) (output : list string) : Prop :=
  Forall primitive_group output /\
  output_chars output = chars_without_spaces input.
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

Definition ascii_of_z_1 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_1 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_1 c) (string_of_list_z_1 rest)
  end.

Definition row_payload_z_1 (row : list Z) : list Z :=
  firstn (Z.to_nat (Zlength row - 1)) row.

Definition row_string_z_1 (row : list Z) : string :=
  string_of_list_z_1 (row_payload_z_1 row).

Definition rows_to_strings_z_1 (rows : list (list Z)) : list string :=
  map row_string_z_1 rows.

Definition problem_1_pre_z (s : list Z) : Prop :=
  problem_1_pre (string_of_list_z_1 s).

Definition problem_1_spec_z (s : list Z) (rows : list (list Z)) : Prop :=
  problem_1_spec (string_of_list_z_1 s) (rows_to_strings_z_1 rows).

Definition valid_paren_char_1 (c : Z) : Prop :=
  c = 32 \/ c = 40 \/ c = 41.

Definition valid_paren_input_1 (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> valid_paren_char_1 (Znth i s 0).

Definition paren_payload_1 (s : list Z) (start stop : Z) : list Z :=
  sublist start stop s.

Definition paren_row_1 (s : list Z) (start stop : Z) : list Z :=
  c_string (paren_payload_1 s start stop).

Definition paren_step_1
    (s : list Z) (st : list (list Z) * Z * Z) (i c : Z)
    : list (list Z) * Z * Z :=
  let '(rows, level, start) := st in
  if Z.eqb c 40 then
    let start' := if Z.eqb level 0 then i else start in
    (rows, level + 1, start')
  else if Z.eqb c 41 then
    let level' := level - 1 in
    if Z.eqb level' 0 then
      (rows ++ [c_string (sublist start (i + 1) s)], 0, -1)
    else (rows, level', start)
  else (rows, level, start).

Fixpoint paren_state_nat_1 (n : nat) (s : list Z)
  : list (list Z) * Z * Z :=
  match n with
  | O => ([], 0, -1)
  | S n' =>
      paren_step_1
        s
        (paren_state_nat_1 n' s)
        (Z.of_nat n')
        (Znth (Z.of_nat n') s 0)
  end.

Definition paren_completed_rows_1 (s : list Z) (i : Z) : list (list Z) :=
  let '(rows, _, _) := paren_state_nat_1 (Z.to_nat i) s in rows.

Definition paren_scan_level_1 (s : list Z) (i : Z) : Z :=
  let '(_, level, _) := paren_state_nat_1 (Z.to_nat i) s in level.

Definition paren_scan_start_1 (s : list Z) (i : Z) : Z :=
  let '(_, _, start) := paren_state_nat_1 (Z.to_nat i) s in start.

Definition paren_output_rows_1 (s : list Z) : list (list Z) :=
  paren_completed_rows_1 s (Zlength s).

Definition paren_safe_input_1 (s : list Z) : Prop :=
  (forall i,
    0 <= i < Zlength s ->
    Znth i (c_string s) 0 = 41 ->
    0 < paren_scan_level_1 s i) /\
  paren_scan_level_1 s (Zlength s) = 0 /\
  paren_scan_start_1 s (Zlength s) = -1 /\
  problem_1_spec_z s (paren_output_rows_1 s).

Definition paren_scan_state_1
    (s : list Z) (i level start : Z) (rows : list (list Z)) : Prop :=
  0 <= i <= string_length s /\
  rows = paren_completed_rows_1 s i /\
  level = paren_scan_level_1 s i /\
  start = paren_scan_start_1 s i /\
  0 <= level /\
  ((level = 0 /\ start = -1) \/ (level > 0 /\ 0 <= start < i)).

Fixpoint paren_rows_heap_1
    (row_ptrs : list Z) (rows : list (list Z)) : Assertion :=
  match row_ptrs, rows with
  | p :: ps, row :: rs =>
      CharArray.full p (Zlength row) row ** paren_rows_heap_1 ps rs
  | _, _ => emp
  end.
