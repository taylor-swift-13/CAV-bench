(* def bf(planet1, planet2):
'''
There are eight planets in our solar system: the closerst to the Sun
is Mercury, the next one is Venus, then Earth, Mars, Jupiter, Saturn,
Uranus, Neptune.
Write a function that takes two planet names as strings planet1 and planet2.
The function should return a tuple containing all planets whose orbits are
located between the orbit of planet1 and the orbit of planet2, sorted by
the proximity to the sun.
The function should return an empty tuple if planet1 or planet2
are not correct planet names.
Examples
bf("Jupiter", "Neptune") ==> ("Saturn", "Uranus")
bf("Earth", "Mercury") ==> ("Venus")
bf("Mercury", "Uranus") ==> ("Venus", "Earth", "Mars", "Jupiter", "Saturn")
''' *)
(* 引入必要的 Coq 库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Import ListNotations.

(* 定义行星名称为 string，并按与太阳的距离排序 *)
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition solar_system : list string :=
  [ "Mercury"; "Venus"; "Earth"; "Mars"; "Jupiter"; "Saturn"; "Uranus"; "Neptune" ].


(* 辅助函数：获取一个行星在 solar_system 列表中的索引 (位置)。
   不使用递归实现，而是用 fold_left 从左到右遍历并记录索引。
   累加器是 (current_index, found_option)，当找到匹配时记录当前位置。 *)
Definition get_planet_index (p_name : string) : option nat :=
  snd (
    fold_left (fun acc p =>
      let '(i, res) := acc in
      match res with
      | Some _ => (S i, res)
      | None => if String.eqb p p_name then (S i, Some i) else (S i, None)
      end) solar_system (0, None)).

(*
  bf 函数的程序规约 (Spec)
  - 输入: planet1 (list ascii), planet2 (list ascii)
  - 输出: result (list (list ascii))
*)
(* 独立的输入前置条件 *)
Definition problem_148_pre (planet1 planet2 : string) : Prop := True.

Definition problem_148_spec (planet1 planet2 : string) (result : list string) : Prop :=
  match (get_planet_index planet1), (get_planet_index planet2) with
  | Some idx1, Some idx2 =>
    (* --- 情况 1: planet1 和 planet2 都是有效的行星名称 --- *)
    let min_idx := min idx1 idx2 in
    let max_idx := max idx1 idx2 in

    (* 属性 1: 输出列表 `result` 中的每个行星 `p`，当且仅当 `p` 的轨道
       位置在 `planet1` 和 `planet2` 的轨道之间。*)
    (forall p, In p result <->
      (exists idx, get_planet_index p = Some idx /\
                   min_idx < idx < max_idx))
    /\
    (* 属性 2: 输出列表 `result` 必须是根据与太阳的距离排序的。*)
    (forall p_a p_b i j,
      nth_error result i = Some p_a ->
      nth_error result j = Some p_b ->
      i < j ->
      (exists idx_a idx_b,
         get_planet_index p_a = Some idx_a /\
         get_planet_index p_b = Some idx_b /\
         idx_a < idx_b))

  | _, _ =>
    (* --- 情况 2: planet1 或 planet2 不是有效的行星名称 --- *)
    (* 输出 `result` 必须为空列表。*)
    result = []
  end.


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

Definition ascii_of_z_148 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_148 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_148 c) (string_of_list_z_148 rest)
  end.

Definition problem_148_pre_z (p1 p2 : list Z) : Prop :=
  problem_148_pre (string_of_list_z_148 p1) (string_of_list_z_148 p2).

Definition problem_148_spec_z
    (p1 p2 : list Z) (output_rows : list (list Z)) : Prop :=
  problem_148_spec
    (string_of_list_z_148 p1)
    (string_of_list_z_148 p2)
    (map string_of_list_z_148 output_rows).

Definition mercury_literal_148 : string := "Mercury"%string.
Definition venus_literal_148 : string := "Venus"%string.
Definition earth_literal_148 : string := "Earth"%string.
Definition mars_literal_148 : string := "Mars"%string.
Definition jupiter_literal_148 : string := "Jupiter"%string.
Definition saturn_literal_148 : string := "Saturn"%string.
Definition uranus_literal_148 : string := "Uranus"%string.
Definition neptune_literal_148 : string := "Neptune"%string.

Definition all_planet_literals_148 : list string :=
  [mercury_literal_148; venus_literal_148; earth_literal_148; mars_literal_148;
   jupiter_literal_148; saturn_literal_148; uranus_literal_148; neptune_literal_148].

Definition lit_payload_148 (s : string) : list Z :=
  StringToList s (StringLength s).

Definition planet_literal_148 (i : Z) : string :=
  match i with
  | 0%Z => mercury_literal_148
  | 1%Z => venus_literal_148
  | 2%Z => earth_literal_148
  | 3%Z => mars_literal_148
  | 4%Z => jupiter_literal_148
  | 5%Z => saturn_literal_148
  | 6%Z => uranus_literal_148
  | 7%Z => neptune_literal_148
  | _ => EmptyString
  end.

Definition planet_payload_148 (i : Z) : list Z :=
  lit_payload_148 (planet_literal_148 i).

Definition planet_payloads_string_safe_148 : Prop :=
  string_lib.valid_string (planet_payload_148 0) /\
  string_lib.valid_string (planet_payload_148 1) /\
  string_lib.valid_string (planet_payload_148 2) /\
  string_lib.valid_string (planet_payload_148 3) /\
  string_lib.valid_string (planet_payload_148 4) /\
  string_lib.valid_string (planet_payload_148 5) /\
  string_lib.valid_string (planet_payload_148 6) /\
  string_lib.valid_string (planet_payload_148 7) /\
  string_lib.string_length (planet_payload_148 0) < INT_MAX /\
  string_lib.string_length (planet_payload_148 1) < INT_MAX /\
  string_lib.string_length (planet_payload_148 2) < INT_MAX /\
  string_lib.string_length (planet_payload_148 3) < INT_MAX /\
  string_lib.string_length (planet_payload_148 4) < INT_MAX /\
  string_lib.string_length (planet_payload_148 5) < INT_MAX /\
  string_lib.string_length (planet_payload_148 6) < INT_MAX /\
  string_lib.string_length (planet_payload_148 7) < INT_MAX.

Definition planet_ptr_148 (LM : string -> Z) (i : Z) : Z :=
  LM (planet_literal_148 i).

Definition planet_index_z_148 (p : list Z) : Z :=
  match get_planet_index (string_of_list_z_148 p) with
  | Some n => Z.of_nat n
  | None => -1
  end.

Definition planet_scan_state_148 (p : list Z) (k pos : Z) : Prop :=
  0 <= k <= 8 /\
  -1 <= pos <= 7 /\
  ((planet_index_z_148 p = -1 /\ pos = -1) \/
   (0 <= planet_index_z_148 p <= 7 /\
    ((k <= planet_index_z_148 p /\ pos = -1) \/
     (planet_index_z_148 p < k /\ pos = planet_index_z_148 p)))).

Definition valid_planet_index_148 (i : Z) : bool :=
  andb (Z.leb 0 i) (Z.leb i 7).

Definition between_bounds_148 (i j : Z) : Z * Z :=
  if Z.leb i j then (i, j) else (j, i).

Definition planet_min_index_148 (i j : Z) : Z :=
  if Z.leb i j then i else j.

Definition planet_max_index_148 (i j : Z) : Z :=
  if Z.leb i j then j else i.

Definition candidate_indices_148 : list Z := [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z].

Definition candidate_prefix_148 (k : Z) : list Z :=
  firstn (Z.to_nat k) candidate_indices_148.

Definition index_between_148 (lo hi idx : Z) : bool :=
  andb (Z.ltb lo idx) (Z.ltb idx hi).

Definition selected_indices_prefix_148 (lo hi k : Z) : list Z :=
  filter (fun idx => index_between_148 lo hi idx) (candidate_prefix_148 k).

Definition selected_indices_148 (i j : Z) : list Z :=
  if andb (valid_planet_index_148 i) (valid_planet_index_148 j) then
    let '(lo, hi) := between_bounds_148 i j in
    selected_indices_prefix_148 lo hi 6
  else [].

Definition planet_between_rows_148 (i j : Z) : list (list Z) :=
  map planet_payload_148 (selected_indices_148 i j).

Definition planet_between_ptrs_148 (LM : string -> Z) (i j : Z) : list Z :=
  map (planet_ptr_148 LM) (selected_indices_148 i j).

Definition planet_literals_heap_148 (LM : string -> Z) : Assertion :=
  string_lib.store_string (planet_ptr_148 LM 0) (planet_payload_148 0) **
  string_lib.store_string (planet_ptr_148 LM 1) (planet_payload_148 1) **
  string_lib.store_string (planet_ptr_148 LM 2) (planet_payload_148 2) **
  string_lib.store_string (planet_ptr_148 LM 3) (planet_payload_148 3) **
  string_lib.store_string (planet_ptr_148 LM 4) (planet_payload_148 4) **
  string_lib.store_string (planet_ptr_148 LM 5) (planet_payload_148 5) **
  string_lib.store_string (planet_ptr_148 LM 6) (planet_payload_148 6) **
  string_lib.store_string (planet_ptr_148 LM 7) (planet_payload_148 7) **
  GlobalStrings_missing LM all_planet_literals_148.

Definition output_state_148
    (LM : string -> Z) (lo hi k : Z)
    (rows : list (list Z)) (ptrs : list Z) : Prop :=
  0 <= k <= 7 /\
  rows = map planet_payload_148 (selected_indices_prefix_148 lo hi k) /\
  ptrs = map (planet_ptr_148 LM) (selected_indices_prefix_148 lo hi k).

Definition strcmp_eq_payload_148
    (lit_payload input_payload : list Z) (ret : Z) : Prop :=
  strcmp_result lit_payload input_payload ret /\ (ret = 0 -> lit_payload = input_payload).
