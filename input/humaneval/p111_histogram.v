(* Given a string representing a space separated lowercase letters, return a dictionary
of the letter with the most repetition and containing the corresponding count.
If several letters have the same occurrence, return all of them.

Example:
histogram('a b c') == {'a': 1, 'b': 1, 'c': 1}
histogram('a b b a') == {'a': 2, 'b': 2}
histogram('a b c a b') == {'a': 2, 'b': 2}
histogram('b b b b a') == {'b': 4}
histogram('') == {}
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope bool_scope.


(* 辅助函数：过滤掉空格 *)
Definition filter_spaces (l : list ascii) : list ascii :=
  filter (fun c => if ascii_dec c " "%char then false else true) l.

(* 辅助函数：计算字符在列表中的出现次数 *)
Definition count_char (letters : list ascii) (c : ascii) : nat :=
  count_occ ascii_dec letters c.

(* 辅助函数：计算列表中出现次数最多的次数 *)
Definition get_max_count (letters : list ascii) : nat :=
  let unique_letters := nodup ascii_dec letters in
  let counts := map (count_char letters) unique_letters in
  fold_right max 0 counts.

(* 仅包含空格或小写字母 *)
Definition problem_111_pre (s : string) : Prop :=
  let letters := list_ascii_of_string s in
  Forall (fun c => c = " "%char \/ let n := nat_of_ascii c in 97 <= n /\ n <= 122) letters.

(*
  程序规约 Spec
  输入：s : string (一个由字符组成的字符串)
  输出：res : list (ascii * nat) (一个由 (字符, 计数值) 对组成的列表)
*)
Definition problem_111_spec (s : string) (res : list (ascii * nat)) : Prop :=
  let raw_letters := list_ascii_of_string s in
  let letters := filter_spaces raw_letters in
  let unique_letters := nodup ascii_dec letters in
  match unique_letters with
  | [] => res = [] (* 如果输入列表为空，则输出也为空 *)
  | _ :: _ => (* 如果列表不为空 *)
    let max_count := get_max_count letters in

    (*
      规约的核心：输出 res 必须精确地包含所有出现次数最多的字符及其计数值。
      这可以用两个方向的蕴含来表达。
    *)
    (* 1. "Soundness": 输出 res 中的每一个元素都必须是正确的。 *)
    (forall (p : ascii * nat), In p res ->
      let (c, n) := p in
      n = max_count /\ count_char letters c = max_count) /\

    (* 2. "Completeness": 每一个符合条件的字符都必须出现在输出 res 中。 *)
    (forall c, In c unique_letters ->
      count_char letters c = max_count ->
      In (c, max_count) res)
  end.

(* Definition-only adapters for C strings and parallel result arrays. *)
Definition ascii_of_z_111 (z : Z) : ascii := ascii_of_nat (Z.to_nat z).
Fixpoint string_of_list_z_111 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | z :: tl => String (ascii_of_z_111 z) (string_of_list_z_111 tl)
  end.

Fixpoint zip_histogram_111 (keys values : list Z) : list (ascii * nat) :=
  match keys, values with
  | k :: keys', v :: values' =>
      (ascii_of_z_111 k, Z.to_nat v) :: zip_histogram_111 keys' values'
  | _, _ => []
  end.

Definition problem_111_pre_z (input : list Z) : Prop :=
  problem_111_pre (string_of_list_z_111 input).

Definition problem_111_spec_z
    (input keys values : list Z) : Prop :=
  List.length keys = List.length values /\
  Forall (fun z => (0 <= z)%Z) values /\
  problem_111_spec (string_of_list_z_111 input)
                   (zip_histogram_111 keys values).

Definition non_space_111 (z : Z) : bool := negb (Z.eqb z 32).

Definition prefix_letters_111 (input : list Z) (i : Z) : list Z :=
  filter non_space_111 (firstn (Z.to_nat i) input).

Definition count_byte_111 (letters : list Z) (z : Z) : Z :=
  Z.of_nat (count_occ Z.eq_dec letters z).

Definition byte_domain_111 : list Z := map Z.of_nat (seq 0 256).

Definition counts_at_111 (input : list Z) (i : Z) : list Z :=
  map (count_byte_111 (prefix_letters_111 input i)) byte_domain_111.

Definition max_count_z_111 (counts : list Z) : Z :=
  fold_right Z.max 0%Z counts.

Definition problem_111_scan_state_z
    (input : list Z) (i : Z) (counts : list Z) (max_count : Z) : Prop :=
  counts = counts_at_111 input i /\ max_count = max_count_z_111 counts /\
  (forall z : Z, (0 <= z < 256)%Z -> (0 <= Znth z counts 0 <= i)%Z).

Definition selected_keys_111
    (counts : list Z) (max_count limit : Z) : list Z :=
  filter (fun z => Z.eqb (Znth z counts 0%Z) max_count && Z.ltb 0%Z max_count)
         (map Z.of_nat (seq 0 (Z.to_nat limit))).

Definition selected_values_111
    (counts : list Z) (max_count limit : Z) : list Z :=
  map (fun z => Znth z counts 0%Z) (selected_keys_111 counts max_count limit).

Definition problem_111_output_prefix_z
    (counts : list Z) (max_count limit : Z)
    (keys values : list Z) : Prop :=
  keys = selected_keys_111 counts max_count limit /\
  values = selected_values_111 counts max_count limit.
