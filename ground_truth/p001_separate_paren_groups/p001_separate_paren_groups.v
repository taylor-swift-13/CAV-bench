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

Lemma paren_rows_heap_1_nil :
  emp |-- paren_rows_heap_1 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma paren_rows_heap_1_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  paren_rows_heap_1 ptrs rows ** CharArray.full p (Zlength row) row
  |-- paren_rows_heap_1 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows).
    lia.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs).
    lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma String_length_string_of_list_z_1 : forall l,
  String.length (string_of_list_z_1 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_payload_c_string_1 : forall payload,
  row_payload_z_1 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_1, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite Zlength_correct.
  replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
    with (Z.of_nat (List.length payload)) by lia.
  rewrite Nat2Z.id.
  replace (List.length payload) with (List.length payload + 0)%nat by lia.
  rewrite firstn_app_2.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma rows_to_strings_c_string_1 : forall payloads,
  rows_to_strings_z_1 (map c_string payloads) =
  map string_of_list_z_1 payloads.
Proof.
  induction payloads as [| p ps IH]; simpl; [reflexivity|].
  unfold row_string_z_1.
  rewrite row_payload_c_string_1.
  rewrite IH.
  reflexivity.
Qed.

Lemma Zlength_map_1 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma Zlength_paren_payload_1 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (paren_payload_1 s start stop) = stop - start.
Proof.
  intros s start stop Hlo Hhi.
  unfold paren_payload_1.
  rewrite Zlength_sublist; lia.
Qed.

Lemma paren_payload_c_string_1 : forall s start stop,
  0 <= start <= stop ->
  stop <= string_length s ->
  sublist start stop (c_string s) = paren_payload_1 s start stop.
Proof.
  intros s start stop Hlo Hhi.
  unfold paren_payload_1, c_string, string_length in *.
  apply sublist_split_app_l; lia.
Qed.

Lemma paren_scan_state_1_initial : forall s,
  paren_scan_state_1 s 0 0 (-1) [].
Proof.
  intros s.
  unfold paren_scan_state_1, paren_completed_rows_1,
    paren_scan_level_1, paren_scan_start_1, string_length.
  simpl.
  repeat split; try rewrite Zlength_correct; try lia; auto.
Qed.

Lemma paren_state_nat_1_step : forall i s,
  0 <= i ->
  paren_state_nat_1 (Z.to_nat (i + 1)) s =
  paren_step_1 s (paren_state_nat_1 (Z.to_nat i) s) i (Znth i s 0).
Proof.
  intros i s Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma c_string_Znth_before_1 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma paren_payload_1_empty : forall s start,
  paren_payload_1 s start start = [].
Proof.
  intros s start.
  unfold paren_payload_1.
  apply sublist_nil.
  lia.
Qed.

Lemma paren_payload_1_step : forall s start i,
  0 <= start <= i ->
  i < Zlength s ->
  paren_payload_1 s start (i + 1) =
  paren_payload_1 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds Hi.
  unfold paren_payload_1.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry; apply sublist_single; lia.
Qed.

Lemma paren_payload_1_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  paren_payload_1 s start (start + (k + 1)) =
  paren_payload_1 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite paren_payload_1_step by lia.
  rewrite c_string_Znth_before_1 by lia.
  reflexivity.
Qed.

Lemma paren_row_1_unfold : forall s start stop,
  paren_row_1 s start stop = paren_payload_1 s start stop ++ [0].
Proof.
  intros.
  unfold paren_row_1, c_string.
  reflexivity.
Qed.

Lemma paren_scan_state_1_change_level : forall s i level level' start rows,
  paren_scan_state_1 s i level start rows ->
  level = level' ->
  paren_scan_state_1 s i level' start rows.
Proof.
  intros; subst; auto.
Qed.

Lemma paren_scan_state_1_step_open_continue : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  level <> 0 ->
  Znth i (c_string s) 0 = 40 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) (level + 1) start rows.
Proof.
  intros s i level start rows Hstate Hlevel Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    assert (Hlevel0 : level0 <> 0).
    { intro Hz; apply Hlevel; rewrite Hlev; exact Hz. }
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    assert (Hlevel0 : level0 <> 0).
    { intro Hz; apply Hlevel; lia. }
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    assert (Hlevel0 : level0 <> 0).
    {
      intro Hz.
      apply Hlevel.
      rewrite Hlev.
      unfold paren_scan_level_1.
      rewrite Hst.
      simpl.
      exact Hz.
    }
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
Qed.

Lemma paren_scan_state_1_step_open_start : forall s i rows,
  paren_scan_state_1 s i 0 (-1) rows ->
  Znth i (c_string s) 0 = 40 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) 1 i rows.
Proof.
  intros s i rows Hstate Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst rows.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite <- Hlev.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite <- Hlev.
    rewrite Z.eqb_refl.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_space : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  Znth i (c_string s) 0 = 32 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) level start rows.
Proof.
  intros s i level start rows Hstate Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_close_finish : forall s i start rows,
  paren_scan_state_1 s i 1 start rows ->
  0 <= start <= i ->
  Znth i (c_string s) 0 = 41 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) 0 (-1)
    (rows ++ [paren_row_1 s start (i + 1)]).
Proof.
  intros s i start rows Hstate Hstart_bounds Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst rows start0.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    unfold paren_row_1, paren_payload_1.
    reflexivity.
  - unfold paren_scan_level_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_close_continue : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  paren_safe_input_1 s ->
  level - 1 <> 0 ->
  Znth i (c_string s) 0 = 41 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) (level - 1) start rows.
Proof.
  intros s i level start rows Hstate Hsafe Hlevel Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  assert (Hpos : 0 < level).
  {
    unfold paren_safe_input_1 in Hsafe.
    destruct Hsafe as [Hsafe _].
    specialize (Hsafe i ltac:(unfold string_length in *; lia) Hch).
    unfold paren_scan_state_1 in *.
    lia.
  }
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
  - unfold paren_scan_level_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    subst level.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
  - unfold paren_scan_start_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
Qed.

Lemma valid_paren_input_1_space : forall s i,
  valid_paren_input_1 s ->
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 <> 41 ->
  Znth i (c_string s) 0 <> 40 ->
  Znth i (c_string s) 0 = 32.
Proof.
  intros s i Hvalid Hi Hnot_close Hnot_open.
  rewrite c_string_Znth_before_1 by lia.
  unfold valid_paren_input_1, valid_paren_char_1 in Hvalid.
  specialize (Hvalid i Hi).
  rewrite c_string_Znth_before_1 in Hnot_close by lia.
  rewrite c_string_Znth_before_1 in Hnot_open by lia.
  destruct Hvalid as [Hspace | [Hopen | Hclose]]; congruence.
Qed.

Lemma paren_scan_state_1_level0_start : forall s i start rows,
  paren_scan_state_1 s i 0 start rows ->
  start = -1.
Proof.
  intros s i start rows Hstate.
  unfold paren_scan_state_1 in Hstate.
  destruct Hstate as [_ [_ [_ [_ [_ Hcases]]]]].
  destruct Hcases as [[_ Hstart] | [Hbad _]]; lia.
Qed.

Lemma paren_scan_state_1_nonzero_start : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  level <> 0 ->
  0 <= start.
Proof.
  intros s i level start rows Hstate Hlevel.
  unfold paren_scan_state_1 in Hstate.
  destruct Hstate as [_ [_ [_ [_ [_ Hcases]]]]].
  destruct Hcases as [[Hzero _] | [_ [Hstart _]]]; lia.
Qed.
