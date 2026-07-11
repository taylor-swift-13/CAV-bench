(* Given an array of integers, sort the integers that are between 1 and 9 inclusive,
reverse the resulting array, and then replace each digit by its corresponding name from
"One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".

For example:
arr = [2, 1, 1, 4, 5, 8, 2, 3]
-> sort arr -> [1, 1, 2, 2, 3, 4, 5, 8]
-> reverse arr -> [8, 5, 4, 3, 2, 2, 1, 1]
return ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]

If the array is empty, return an empty array:
arr = []
return []

If the array has any strange number ignore it:
arr = [1, -1 , 55]
-> sort arr -> [-1, 1, 55]
-> reverse arr -> [55, 1, -1]
return = ['One'] *)

(* 引入所需的Coq标准库 *)
Require Import Coq.Lists.List.      (* List 操作, 包括 Permutation *)
Require Import Coq.Strings.String.  (* String 类型 *)
Require Import Coq.ZArith.ZArith.    (* Z整数类型及其操作 *)
Require Import Coq.Sorting.Sorted.     (* 引入 Sorted 属性的定义 *)
Require Import Permutation.
Import ListNotations. (* 启用列表的 [a; b; c] 写法 *)
Open Scope Z_scope.



(*
  辅助函数 (1):
  定义一个布尔函数，用于检查一个整数 `z` 是否在 1 到 9 之间（包含边界）。
*)
Definition is_target_digit (z : Z) : bool :=
  (1 <=? z) && (z <=? 9).

(*
  辅助函数 (2):
  将一个 1 到 9 的整数转换为其对应的英文单词字符串。
*)
Definition digit_to_word (z : Z) : string :=
  match z with
  | 1 => "One"%string
  | 2 => "Two"%string
  | 3 => "Three"%string
  | 4 => "Four"%string
  | 5 => "Five"%string
  | 6 => "Six"%string
  | 7 => "Seven"%string
  | 8 => "Eight"%string
  | 9 => "Nine"%string
  | _ => ""%string
  end.
(* 输入可以包含任意整数 *)

Definition problem_105_pre (l_in : list Z) : Prop := True.

(*
  程序规约 (Program Specification):
  这是一个 Prop (命题)，它表达了输入列表 l_in 和输出列表 l_out 之间的关系。
  这次我们使用声明式的方式来定义排序。
*)
Definition problem_105_spec (l_in : list Z) (l_out : list string) : Prop :=
  (* 步骤 1: 筛选出 l_in 中所有 1 到 9 之间的整数 *)
  let l_filtered := filter is_target_digit l_in in

  (*
    步骤 2: 声明存在一个中间列表 `l_sorted`，它满足排序的属性。
    这是一种更符合Coq风格的规约写法。
  *)
  exists (l_sorted : list Z),
    (* 属性a: l_sorted 是 l_filtered 的一个排列 *)
    (Permutation l_filtered l_sorted /\
    (* 属性b: l_sorted 是根据小于等于关系升序排列的 *)
     Sorted Z.le l_sorted) /\
    (* 步骤 3 & 4: 后续步骤与之前相同，基于这个满足属性的 l_sorted 进行 *)
    let l_reversed := rev l_sorted in
    l_out = map digit_to_word l_reversed.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import SimpleC.StdLib.string_lib.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.

Parameter LitMap : string -> addr.

Definition ascii_of_z_105 (z : Z) : ascii :=
  ascii_of_nat (Z.to_nat z).

Fixpoint string_of_list_z_105 (l : list Z) : string :=
  match l with
  | [] => EmptyString
  | c :: rest => String (ascii_of_z_105 c) (string_of_list_z_105 rest)
  end.

Definition problem_105_pre_z (l : list Z) : Prop :=
  problem_105_pre l /\
  Forall (fun z => INT_MIN <= z <= INT_MAX) l.

Definition int_range_list_105 (l : list Z) : Prop :=
  Forall (fun z => INT_MIN <= z <= INT_MAX) l.

Lemma int_range_list_105_perm : forall a b,
  int_range_list_105 a ->
  Permutation a b ->
  int_range_list_105 b.
Proof.
  unfold int_range_list_105.
  intros a b Ha Hperm.
  eapply Permutation_Forall; eauto.
Qed.

Lemma int_range_list_105_Znth : forall l i,
  int_range_list_105 l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 <= INT_MAX.
Proof.
  intros l i Hrange Hi.
  unfold int_range_list_105 in Hrange.
  apply Forall_forall with (x := Znth i l 0) in Hrange.
  - exact Hrange.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Definition problem_105_spec_z (input : list Z) (output_rows : list (list Z)) : Prop :=
  problem_105_spec input (map string_of_list_z_105 output_rows).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Definition copy_prefix_105 (input : list Z) (i : Z) : list Z :=
  sublist 0 i input.

Lemma copy_prefix_105_Zlength : forall input i,
  0 <= i <= Zlength input ->
  Zlength (copy_prefix_105 input i) = i.
Proof.
  intros input i Hi.
  unfold copy_prefix_105.
  rewrite Zlength_correct.
  rewrite sublist_length by lia.
  lia.
Qed.

Lemma copy_prefix_105_snoc : forall input i,
  0 <= i < Zlength input ->
  copy_prefix_105 input (i + 1) =
  copy_prefix_105 input i ++ [Znth i input 0].
Proof.
  intros input i Hi.
  unfold copy_prefix_105.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  reflexivity.
Qed.

Definition one_literal_105 : string := "One"%string.
Definition two_literal_105 : string := "Two"%string.
Definition three_literal_105 : string := "Three"%string.
Definition four_literal_105 : string := "Four"%string.
Definition five_literal_105 : string := "Five"%string.
Definition six_literal_105 : string := "Six"%string.
Definition seven_literal_105 : string := "Seven"%string.
Definition eight_literal_105 : string := "Eight"%string.
Definition nine_literal_105 : string := "Nine"%string.

Definition all_digit_literals_105 : list string :=
  [one_literal_105].

Definition lit_payload_105 (s : string) : list Z :=
  StringToList s (StringLength s).

Definition digit_literal_105 (d : Z) : string :=
  match d with
  | 1%Z => one_literal_105
  | 2%Z => two_literal_105
  | 3%Z => three_literal_105
  | 4%Z => four_literal_105
  | 5%Z => five_literal_105
  | 6%Z => six_literal_105
  | 7%Z => seven_literal_105
  | 8%Z => eight_literal_105
  | 9%Z => nine_literal_105
  | _ => EmptyString
  end.

Definition digit_payload_105 (d : Z) : list Z :=
  lit_payload_105 (digit_literal_105 d).

Definition digit_ptr_105 (LM : string -> Z) (d : Z) : Z :=
  LM (digit_literal_105 d).

Definition digit_payloads_string_safe_105 : Prop :=
  string_lib.valid_string (digit_payload_105 1) /\
  string_lib.valid_string (digit_payload_105 2) /\
  string_lib.valid_string (digit_payload_105 3) /\
  string_lib.valid_string (digit_payload_105 4) /\
  string_lib.valid_string (digit_payload_105 5) /\
  string_lib.valid_string (digit_payload_105 6) /\
  string_lib.valid_string (digit_payload_105 7) /\
  string_lib.valid_string (digit_payload_105 8) /\
  string_lib.valid_string (digit_payload_105 9) /\
  string_lib.string_length (digit_payload_105 1) < INT_MAX /\
  string_lib.string_length (digit_payload_105 2) < INT_MAX /\
  string_lib.string_length (digit_payload_105 3) < INT_MAX /\
  string_lib.string_length (digit_payload_105 4) < INT_MAX /\
  string_lib.string_length (digit_payload_105 5) < INT_MAX /\
  string_lib.string_length (digit_payload_105 6) < INT_MAX /\
  string_lib.string_length (digit_payload_105 7) < INT_MAX /\
  string_lib.string_length (digit_payload_105 8) < INT_MAX /\
  string_lib.string_length (digit_payload_105 9) < INT_MAX.

Lemma Znth_In_range_105 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Ltac destruct_digit_105 d Hd :=
  let Hcases := fresh "Hcases" in
  assert (d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) as Hcases by lia;
  repeat (destruct Hcases as [Hcases | Hcases];
          [subst d |]);
  [ idtac | idtac | idtac | idtac | idtac | idtac | idtac | idtac | subst d ].

Lemma digit_payload_ascii_105 : forall d c,
  1 <= d <= 9 ->
  In c (digit_payload_105 d) ->
  0 <= c <= 127.
Proof.
  intros d c Hd Hin.
  destruct_digit_105 d Hd;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma digit_payload_nonzero_105 : forall d c,
  1 <= d <= 9 ->
  In c (digit_payload_105 d) ->
  c <> 0.
Proof.
  intros d c Hd Hin.
  destruct_digit_105 d Hd;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma digit_payload_valid_string_105 : forall d,
  1 <= d <= 9 ->
  string_lib.valid_string (digit_payload_105 d).
Proof.
  intros d Hd.
  unfold string_lib.valid_string, string_lib.all_ascii, string_lib.no_inner_nul.
  split; intros i Hi;
    pose proof (Znth_In_range_105 (digit_payload_105 d) i 0 Hi) as Hin.
  - apply digit_payload_ascii_105 with (d := d); assumption.
  - apply digit_payload_nonzero_105 with (d := d); assumption.
Qed.

Lemma digit_payload_length_bound_105 : forall d,
  1 <= d <= 9 ->
  string_lib.string_length (digit_payload_105 d) < INT_MAX.
Proof.
  intros d Hd.
  destruct_digit_105 d Hd;
    unfold string_lib.string_length, digit_payload_105, lit_payload_105,
      digit_literal_105;
    unfold one_literal_105, two_literal_105, three_literal_105,
      four_literal_105, five_literal_105, six_literal_105,
      seven_literal_105, eight_literal_105, nine_literal_105;
    rewrite StringToList_length;
    unfold StringLength; simpl; lia.
Qed.

Lemma digit_payloads_string_safe_105_proof :
  digit_payloads_string_safe_105.
Proof.
  unfold digit_payloads_string_safe_105.
  repeat split;
    try solve
      [ apply digit_payload_valid_string_105; lia
      | apply digit_payload_length_bound_105; lia ].
Qed.

Definition digit_literals_heap_105 (LM : string -> Z) : Assertion :=
  string_lib.store_string (digit_ptr_105 LM 1) (digit_payload_105 1) **
  string_lib.store_string (digit_ptr_105 LM 2) (digit_payload_105 2) **
  string_lib.store_string (digit_ptr_105 LM 3) (digit_payload_105 3) **
  string_lib.store_string (digit_ptr_105 LM 4) (digit_payload_105 4) **
  string_lib.store_string (digit_ptr_105 LM 5) (digit_payload_105 5) **
  string_lib.store_string (digit_ptr_105 LM 6) (digit_payload_105 6) **
  string_lib.store_string (digit_ptr_105 LM 7) (digit_payload_105 7) **
  string_lib.store_string (digit_ptr_105 LM 8) (digit_payload_105 8) **
  string_lib.store_string (digit_ptr_105 LM 9) (digit_payload_105 9) **
  GlobalStrings_missing LM all_digit_literals_105.

Definition target_digit_105 (z : Z) : bool :=
  Z.leb 1 z && Z.leb z 9.

Lemma target_digit_105_true : forall d,
  1 <= d <= 9 ->
  target_digit_105 d = true.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_true_iff.
  split; apply Z.leb_le; lia.
Qed.

Lemma target_digit_105_false_high : forall d,
  d > 9 ->
  target_digit_105 d = false.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_false_iff.
  right.
  apply Z.leb_gt.
  lia.
Qed.

Lemma target_digit_105_false_low : forall d,
  d < 1 ->
  target_digit_105 d = false.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_false_iff.
  left.
  apply Z.leb_gt.
  lia.
Qed.

Definition digit_words_between_105 (sorted_l : list Z) (lo hi : Z) : list (list Z) :=
  map digit_payload_105 (filter target_digit_105 (rev (sublist lo hi sorted_l))).

Definition digit_ptrs_between_105
    (LM : string -> Z) (sorted_l : list Z) (lo hi : Z) : list Z :=
  map (digit_ptr_105 LM) (filter target_digit_105 (rev (sublist lo hi sorted_l))).

Definition output_state_105
    (LM : string -> Z) (sorted_l : list Z) (k : Z)
    (rows : list (list Z)) (ptrs : list Z) : Prop :=
  0 <= k <= Zlength sorted_l /\
  rows = digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l) /\
  ptrs = digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l).

Lemma filtered_rev_sublist_skip_step_105 : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - (k + 1)) (Zlength sorted_l) sorted_l)) =
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - k) (Zlength sorted_l) sorted_l)).
Proof.
  intros sorted_l k d Hk Hd Htarget.
  replace (Zlength sorted_l - (k + 1)) with (Zlength sorted_l - 1 - k) by lia.
  replace (Zlength sorted_l - k) with (Zlength sorted_l - 1 - k + 1) by lia.
  rewrite (sublist_split (Zlength sorted_l - 1 - k)
    (Zlength sorted_l) (Zlength sorted_l - 1 - k + 1) sorted_l) by lia.
  rewrite (sublist_single 0 (Zlength sorted_l - 1 - k) sorted_l) by lia.
  rewrite <- Hd.
  rewrite rev_app_distr.
  simpl.
  rewrite filter_app.
  simpl.
  rewrite Htarget.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma filtered_rev_sublist_hit_step_105 : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - (k + 1)) (Zlength sorted_l) sorted_l)) =
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - k) (Zlength sorted_l) sorted_l)) ++ [d].
Proof.
  intros sorted_l k d Hk Hd Htarget.
  replace (Zlength sorted_l - (k + 1)) with (Zlength sorted_l - 1 - k) by lia.
  replace (Zlength sorted_l - k) with (Zlength sorted_l - 1 - k + 1) by lia.
  rewrite (sublist_split (Zlength sorted_l - 1 - k)
    (Zlength sorted_l) (Zlength sorted_l - 1 - k + 1) sorted_l) by lia.
  rewrite (sublist_single 0 (Zlength sorted_l - 1 - k) sorted_l) by lia.
  rewrite <- Hd.
  rewrite rev_app_distr.
  simpl.
  rewrite filter_app.
  simpl.
  rewrite Htarget.
  reflexivity.
Qed.

Lemma digit_words_between_105_skip_step : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  digit_words_between_105 sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l).
Proof.
  intros sorted_l k d Hk Hd Htarget.
  unfold digit_words_between_105.
  rewrite (filtered_rev_sublist_skip_step_105 sorted_l k d) by auto.
  reflexivity.
Qed.

Lemma digit_ptrs_between_105_skip_step : forall LM sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l).
Proof.
  intros LM sorted_l k d Hk Hd Htarget.
  unfold digit_ptrs_between_105.
  rewrite (filtered_rev_sublist_skip_step_105 sorted_l k d) by auto.
  reflexivity.
Qed.

Lemma digit_words_between_105_hit_step : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  digit_words_between_105 sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l) ++
    [digit_payload_105 d].
Proof.
  intros sorted_l k d Hk Hd Htarget.
  unfold digit_words_between_105.
  rewrite (filtered_rev_sublist_hit_step_105 sorted_l k d) by auto.
  rewrite map_app.
  reflexivity.
Qed.

Lemma digit_ptrs_between_105_hit_step : forall LM sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l) ++
    [digit_ptr_105 LM d].
Proof.
  intros LM sorted_l k d Hk Hd Htarget.
  unfold digit_ptrs_between_105.
  rewrite (filtered_rev_sublist_hit_step_105 sorted_l k d) by auto.
  rewrite map_app.
  reflexivity.
Qed.

Lemma output_state_105_skip_step : forall LM sorted_l k d rows ptrs,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  output_state_105 LM sorted_l k rows ptrs ->
  output_state_105 LM sorted_l (k + 1) rows ptrs.
Proof.
  intros LM sorted_l k d rows ptrs Hk Hd Htarget Hstate.
  destruct Hstate as [Hkbounds [Hrows Hptrs]].
  unfold output_state_105.
  repeat split; try lia.
  - rewrite Hrows.
    symmetry.
    apply (digit_words_between_105_skip_step sorted_l k d); assumption.
  - rewrite Hptrs.
    symmetry.
    apply (digit_ptrs_between_105_skip_step LM sorted_l k d); assumption.
Qed.

Lemma output_state_105_hit_step : forall LM sorted_l k d rows ptrs,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  output_state_105 LM sorted_l k rows ptrs ->
  output_state_105 LM sorted_l (k + 1)
    (rows ++ [digit_payload_105 d]) (ptrs ++ [digit_ptr_105 LM d]).
Proof.
  intros LM sorted_l k d rows ptrs Hk Hd Htarget Hstate.
  destruct Hstate as [Hkbounds [Hrows Hptrs]].
  unfold output_state_105.
  repeat split; try lia.
  - rewrite Hrows.
    symmetry.
    apply (digit_words_between_105_hit_step sorted_l k d); assumption.
  - rewrite Hptrs.
    symmetry.
    apply (digit_ptrs_between_105_hit_step LM sorted_l k d); assumption.
Qed.

Lemma target_digit_105_is_target_digit : forall d,
  target_digit_105 d = is_target_digit d.
Proof.
  intros d.
  unfold target_digit_105, is_target_digit.
  reflexivity.
Qed.

Lemma target_digit_105_true_range : forall d,
  target_digit_105 d = true ->
  1 <= d <= 9.
Proof.
  intros d Htarget.
  unfold target_digit_105 in Htarget.
  apply andb_true_iff in Htarget.
  destruct Htarget as [Hlow Hhigh].
  split; apply Z.leb_le; assumption.
Qed.

Lemma digit_payload_to_word_105 : forall d,
  1 <= d <= 9 ->
  string_of_list_z_105 (digit_payload_105 d) = digit_to_word d.
Proof.
  intros d Hd.
  destruct_digit_105 d Hd; vm_compute; reflexivity.
Qed.

Lemma filter_rev_target_105 : forall l,
  filter target_digit_105 (rev l) = rev (filter target_digit_105 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite filter_app.
    rewrite IH.
    destruct (target_digit_105 x) eqn:Htx; simpl.
    + rewrite Htx. reflexivity.
    + rewrite Htx. rewrite app_nil_r. reflexivity.
Qed.

Lemma Permutation_filter_target_105 : forall l1 l2,
  Permutation l1 l2 ->
  Permutation (filter target_digit_105 l1) (filter target_digit_105 l2).
Proof.
  intros l1 l2 Hperm.
  induction Hperm.
  - constructor.
  - simpl.
    destruct (target_digit_105 x).
    + constructor; assumption.
    + assumption.
  - simpl.
    destruct (target_digit_105 x);
      destruct (target_digit_105 y);
      try apply perm_swap;
      reflexivity.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma Forall_filter_target_105 : forall (P : Z -> Prop) l,
  Forall P l ->
  Forall P (filter target_digit_105 l).
Proof.
  intros P l Hforall.
  apply Forall_forall.
  intros x Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin _].
  apply Forall_forall with (x := x) in Hforall; assumption.
Qed.

Lemma StronglySorted_filter_target_105 : forall l,
  StronglySorted Z.le l ->
  StronglySorted Z.le (filter target_digit_105 l).
Proof.
  intros l Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    destruct (target_digit_105 a).
    + constructor.
      * assumption.
      * apply Forall_filter_target_105; assumption.
    + assumption.
Qed.

Lemma Sorted_filter_target_105 : forall l,
  Sorted Z.le l ->
  Sorted Z.le (filter target_digit_105 l).
Proof.
  intros l Hsorted.
  apply StronglySorted_Sorted.
  apply StronglySorted_filter_target_105.
  apply Sorted_StronglySorted.
  - intros x y z Hxy Hyz; lia.
  - exact Hsorted.
Qed.

Lemma map_digit_payload_words_Forall_105 : forall l,
  Forall (fun d => 1 <= d <= 9) l ->
  map string_of_list_z_105 (map digit_payload_105 l) =
  map digit_to_word l.
Proof.
  intros l Hrange.
  induction Hrange; simpl.
  - reflexivity.
  - rewrite digit_payload_to_word_105 by assumption.
    rewrite IHHrange.
    reflexivity.
Qed.

Lemma Forall_rev_filter_target_range_105 : forall l,
  Forall (fun d => 1 <= d <= 9) (rev (filter target_digit_105 l)).
Proof.
  intros l.
  apply Forall_forall.
  intros d Hin.
  apply in_rev in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Htarget].
  apply target_digit_105_true_range.
  exact Htarget.
Qed.

Lemma problem_105_spec_z_of_output_state_intro : forall input sorted_l output_rows LM output_ptrs,
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output_rows = digit_words_between_105 sorted_l 0 (Zlength sorted_l) ->
  output_ptrs = digit_ptrs_between_105 LM sorted_l 0 (Zlength sorted_l) ->
  problem_105_spec_z input output_rows.
Proof.
  intros input sorted_l output_rows LM output_ptrs Hsorted Hperm Hrows _.
  unfold problem_105_spec_z, problem_105_spec.
  exists (filter is_target_digit sorted_l).
  split.
  - split.
    + replace (filter is_target_digit input)
        with (filter target_digit_105 input)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      replace (filter is_target_digit sorted_l)
        with (filter target_digit_105 sorted_l)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      apply Permutation_filter_target_105.
      exact Hperm.
    + replace (filter is_target_digit sorted_l)
        with (filter target_digit_105 sorted_l)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      unfold sorted_int_list_by in Hsorted.
      simpl in Hsorted.
      apply Sorted_filter_target_105.
      exact Hsorted.
  - subst output_rows.
    unfold digit_words_between_105.
    rewrite sublist_self by (pose proof (Zlength_nonneg sorted_l); lia).
    rewrite filter_rev_target_105.
    replace (filter is_target_digit sorted_l)
      with (filter target_digit_105 sorted_l)
      by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
    apply map_digit_payload_words_Forall_105.
    apply Forall_rev_filter_target_range_105.
Qed.

Definition problem_105_spec_z_of_output_state
    (input sorted_l : list Z) (output_rows : list (list Z))
    (LM : string -> Z) (output_ptrs : list Z) : Prop :=
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output_rows = digit_words_between_105 sorted_l 0 (Zlength sorted_l) ->
  output_ptrs = digit_ptrs_between_105 LM sorted_l 0 (Zlength sorted_l) ->
  problem_105_spec_z input output_rows.

Lemma one_lit_to_store_105 : forall LM,
  store_stringLit (LM one_literal_105) one_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 1) (digit_payload_105 1).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, one_literal_105.
  simpl. entailer!.
Qed.

Lemma two_lit_to_store_105 : forall LM,
  store_stringLit (LM two_literal_105) two_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 2) (digit_payload_105 2).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, two_literal_105.
  simpl. entailer!.
Qed.

Lemma three_lit_to_store_105 : forall LM,
  store_stringLit (LM three_literal_105) three_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 3) (digit_payload_105 3).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, three_literal_105.
  simpl. entailer!.
Qed.

Lemma four_lit_to_store_105 : forall LM,
  store_stringLit (LM four_literal_105) four_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 4) (digit_payload_105 4).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, four_literal_105.
  simpl. entailer!.
Qed.

Lemma five_lit_to_store_105 : forall LM,
  store_stringLit (LM five_literal_105) five_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 5) (digit_payload_105 5).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, five_literal_105.
  simpl. entailer!.
Qed.

Lemma six_lit_to_store_105 : forall LM,
  store_stringLit (LM six_literal_105) six_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 6) (digit_payload_105 6).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, six_literal_105.
  simpl. entailer!.
Qed.

Lemma seven_lit_to_store_105 : forall LM,
  store_stringLit (LM seven_literal_105) seven_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 7) (digit_payload_105 7).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, seven_literal_105.
  simpl. entailer!.
Qed.

Lemma eight_lit_to_store_105 : forall LM,
  store_stringLit (LM eight_literal_105) eight_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 8) (digit_payload_105 8).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, eight_literal_105.
  simpl. entailer!.
Qed.

Lemma nine_lit_to_store_105 : forall LM,
  store_stringLit (LM nine_literal_105) nine_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 9) (digit_payload_105 9).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, nine_literal_105.
  simpl. entailer!.
Qed.
