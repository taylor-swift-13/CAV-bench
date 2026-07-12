Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p117_select_words Require Import p117_select_words_goal.
From SimpleC.EE.CAV.ground_truth_p117_select_words Require Import p117_select_words_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p117_select_words.
Local Open Scope sac.

Ltac crush_zbool :=
  unfold is_consonant_z_117, is_letter_z_117, is_vowel_z_117 in *;
  repeat match goal with
  | |- context[Z.leb ?a ?b] =>
      destruct (Z.leb_spec a b); simpl in *; try lia
  | |- context[Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); subst; simpl in *; try lia
  end; try reflexivity; try lia.

Ltac solve_model_pure :=
  unfold andp, coq_prop, emp, is_unit, ConAssertion.state_empty in *;
  simpl in *; repeat split; try tauto; try lia; try crush_zbool.

Ltac solve_consonant_zero :=
  red; intros; left; solve_model_pure.

Ltac solve_consonant_one :=
  red; intros; right; solve_model_pure.

Ltac solve_c_string_char_bound_117 :=
  match goal with
  | Hvalid : valid_string ?s |- 0 <= Znth ?i (c_string ?s) 0 =>
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)); lia
  | Hvalid : valid_string ?s |- Znth ?i (c_string ?s) 0 <= 127 =>
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)); lia
  end.

Ltac solve_word_payload_goal_117 :=
  match goal with
  | Hstate : select_scan_state_117 ?s ?i ?start ?numc ?need_pre ?rows
      |- select_current_117 ?s ?i ?need_pre = word_payload_117 ?s ?start ?i =>
      apply (proj1 (select_scan_state_117_current_nonempty s i start numc need_pre rows Hstate ltac:(lia)))
  | Hstate : select_scan_state_117 ?s ?i ?start ?numc ?need_pre ?rows
      |- ?numc = count_consonants_z_117 (word_payload_117 ?s ?start ?i) =>
      apply (proj2 (select_scan_state_117_current_nonempty s i start numc need_pre rows Hstate ltac:(lia)))
  | |- Zlength (word_payload_117 ?s ?start ?stop) = ?stop - ?start =>
      apply Zlength_word_payload_117; unfold string_length in *; lia
  end.

Ltac solve_space_goal_117 :=
  match goal with
  | H : Znth ?i (c_string ?s) 0 = 32
      |- is_space_z_117 (Znth ?i (c_string ?s) 0) = true =>
      unfold is_space_z_117; rewrite H; reflexivity
  | H : Znth ?i (c_string ?s) 0 = 32
      |- is_space_z_117 (Znth ?i ?s 0) = true =>
      apply is_space_z_117_true_32; unfold string_length in *; lia || exact H
  | H : Znth ?i (c_string ?s) 0 <> 32
      |- is_space_z_117 (Znth ?i (c_string ?s) 0) = false =>
      unfold is_space_z_117; destruct (Z.eqb_spec (Znth i (c_string s) 0) 32); congruence
  | H : Znth ?i (c_string ?s) 0 <> 32
      |- is_space_z_117 (Znth ?i ?s 0) = false =>
      apply is_space_z_117_false_from_neq; unfold string_length in *; lia || exact H
  end.

Ltac select_entailer :=
  unfold store_string;
  entailer!;
  try solve_c_string_char_bound_117;
  try solve_word_payload_goal_117;
  try solve_space_goal_117;
  try lia.

Lemma proof_of_is_consonant_char_return_wit_1 : is_consonant_char_return_wit_1.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_2 : is_consonant_char_return_wit_2.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_3 : is_consonant_char_return_wit_3.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_4 : is_consonant_char_return_wit_4.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_5 : is_consonant_char_return_wit_5.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_6 : is_consonant_char_return_wit_6.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_7 : is_consonant_char_return_wit_7.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_8 : is_consonant_char_return_wit_8.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_9 : is_consonant_char_return_wit_9.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_10 : is_consonant_char_return_wit_10.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_11 : is_consonant_char_return_wit_11.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_12 : is_consonant_char_return_wit_12.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_13 : is_consonant_char_return_wit_13.
Proof. solve_consonant_zero. Qed.

Lemma proof_of_is_consonant_char_return_wit_14 : is_consonant_char_return_wit_14.
Proof. solve_consonant_one. Qed.

Lemma proof_of_is_consonant_char_return_wit_15 : is_consonant_char_return_wit_15.
Proof. solve_consonant_one. Qed.

Lemma proof_of_select_words_entail_wit_1 : select_words_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  Exists (@nil Z) (@nil (list Z)).
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 (retval + 1)).
  rewrite PtrArray.seg_empty.
  select_entailer.
  - apply select_scan_state_117_initial.
    apply string_length_nonneg.
  - subst retval.
    apply string_length_nonneg.
Qed.

Lemma proof_of_select_words_entail_wit_2 : select_words_entail_wit_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_117 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_117_empty).
  rewrite CharArray.full_empty.
  select_entailer.
Qed.

Lemma proof_of_select_words_entail_wit_3 : select_words_entail_wit_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  rewrite word_payload_117_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_select_words_entail_wit_4 : select_words_entail_wit_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  rewrite CharArray.undef_seg_empty.
  select_entailer.
  rewrite word_row_117_unfold.
  replace (start + k) with i by lia.
  replace (k + 1) with (len + 1) by lia.
  reflexivity.
Qed.

Lemma proof_of_select_words_entail_wit_5 : select_words_entail_wit_5.
Proof.
  constructor; pre_process_default.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_117 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_117 str_l start i) = len + 1).
  {
    rewrite word_row_117_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_117 by (unfold string_length in *; lia).
    lia.
  }
  replace (len + 1) with (Zlength (word_row_117 str_l start i)) by lia.
  sep_apply (select_words_rows_heap_117_app_single
    output_ptrs_2 output_rows_2 w (word_row_117 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
  - eapply (select_scan_state_117_step_space_selected
      str_l i start numc need_pre output_rows_2).
    + unfold string_length, naive_C_Rules.string_length in *; lia.
    + exact PreH30.
    + lia.
    + unfold is_space_z_117 in *.
      apply Z.eqb_eq.
      apply Z.eqb_eq in PreH17.
      pose proof (c_string_Znth_before_117 str_l i ltac:(
        unfold string_length, naive_C_Rules.string_length in *; lia)) as Hcs.
      replace (Znth i str_l 0) with ch.
      * exact PreH17.
      * rewrite PreH16.
        unfold c_string, naive_C_Rules.c_string.
        rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
        reflexivity.
    + lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_select_words_entail_wit_6 : select_words_entail_wit_6.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  eapply (select_scan_state_117_step_space_not_selected
    str_l i start numc need_pre output_rows_2).
  - unfold string_length, naive_C_Rules.string_length in *; lia.
  - exact PreH31.
  - lia.
  - apply is_space_z_117_true_32; unfold string_length, naive_C_Rules.string_length in *; lia || exact PreH3.
  - lia.
Qed.

Lemma proof_of_select_words_entail_wit_7 : select_words_entail_wit_7.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  assert (Hstate_empty :
    select_scan_state_117 str_l i (-1) 0 need_pre output_rows_2).
  {
    unfold select_scan_state_117 in PreH30 |- *.
    destruct PreH30 as [Hi [Hrows [Hempty | Hcur]]].
    - destruct Hempty as [Hcurrent [Hstart Hnumc]].
      split; [exact Hi|].
      split; [exact Hrows|].
      left; repeat split; try assumption; lia.
    - destruct Hcur as [Hstart_bounds _].
      lia.
  }
  eapply (select_scan_state_117_step_space_empty
    str_l i need_pre output_rows_2).
  - unfold string_length, naive_C_Rules.string_length in *; lia.
  - exact Hstate_empty.
  - apply is_space_z_117_true_32.
    + unfold string_length, naive_C_Rules.string_length in *; lia.
    + exact PreH2.
Qed.

Lemma proof_of_select_words_entail_wit_8_1 : select_words_entail_wit_8_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  assert (Hcons : is_consonant_z_117 (Znth i str_l 0) = false).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi.
    exact PreH5.
  }
  assert (Hnext :
    select_scan_state_117 str_l (i + 1)
      (if (start <? 0)%Z then i else start)
      (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
      need_pre output_rows_2).
  {
    eapply (select_scan_state_117_step_nospace
      str_l i start numc need_pre output_rows_2).
    - unfold string_length, naive_C_Rules.string_length in *; lia.
    - exact PreH36.
    - apply is_space_z_117_false_from_neq.
      + unfold string_length, naive_C_Rules.string_length in *; lia.
      + exact PreH8.
  }
  rewrite Hcons in Hnext.
  replace (if (start <? 0)%Z then i else start) with start in Hnext
    by (destruct (Z.ltb_spec start 0); lia).
  replace (numc + 0) with numc in Hnext by lia.
  all: try exact Hnext.
  all: try (apply (proj2 (select_scan_state_117_current_nonempty
    str_l (i + 1) start numc need_pre output_rows_2 Hnext ltac:(lia)))).
  all: try (unfold string_length, naive_C_Rules.string_length in *; lia);
       try reflexivity.
  assert (Hcons2 : is_consonant_z_117 (Znth i str_l 0) = false).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi.
    exact PreH5.
  }
  assert (Hnext2 :
    select_scan_state_117 str_l (i + 1) start numc need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons2 in Hraw.
    replace (if (start <? 0)%Z then i else start) with start in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    replace (numc + 0) with numc in Hraw by lia.
    exact Hraw.
  }
  destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) start numc need_pre output_rows_2 Hnext2 ltac:(lia))
    as [Hcur_next Hcnt_next].
  rewrite Hcur_next.
  exact Hcnt_next.
Qed.

Lemma proof_of_select_words_entail_wit_8_2 : select_words_entail_wit_8_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  assert (Hcons : is_consonant_z_117 (Znth i str_l 0) = false).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnumc0 : numc = 0).
  {
    unfold select_scan_state_117 in PreH36.
    destruct PreH36 as [_ [_ [Hempty | Hcur]]].
    - destruct Hempty as [_ [_ Hnumc]]; exact Hnumc.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  assert (Hnext :
    select_scan_state_117 str_l (i + 1) i 0 need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons in Hraw.
    replace (if (start <? 0)%Z then i else start) with i in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    rewrite Hnumc0 in Hraw.
    replace (0 + 0) with 0 in Hraw by lia.
    exact Hraw.
  }
  all: try exact Hnext.
  all: try (destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) i 0 need_pre output_rows_2 Hnext ltac:(lia))
    as [Hcur_next Hcnt_next]; rewrite Hcur_next; exact Hcnt_next).
  all: try (unfold string_length, naive_C_Rules.string_length in *; lia);
       try reflexivity.
  assert (Hcons2 : is_consonant_z_117 (Znth i str_l 0) = false).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnumc02 : numc = 0).
  {
    unfold select_scan_state_117 in PreH36.
    destruct PreH36 as [_ [_ [Hempty | Hcur]]].
    - destruct Hempty as [_ [_ Hnumc]]; exact Hnumc.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  assert (Hnext2 :
    select_scan_state_117 str_l (i + 1) i 0 need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons2 in Hraw.
    replace (if (start <? 0)%Z then i else start) with i in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    rewrite Hnumc02 in Hraw.
    replace (0 + 0) with 0 in Hraw by lia.
    exact Hraw.
  }
  destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) i 0 need_pre output_rows_2 Hnext2 ltac:(lia))
    as [Hcur_next Hcnt_next].
  rewrite Hcur_next.
  exact Hcnt_next.
Qed.

Lemma proof_of_select_words_entail_wit_8_3 : select_words_entail_wit_8_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  assert (Hcons : is_consonant_z_117 (Znth i str_l 0) = true).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnext :
    select_scan_state_117 str_l (i + 1) start (numc + 1) need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons in Hraw.
    replace (if (start <? 0)%Z then i else start) with start in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    exact Hraw.
  }
  all: try exact Hnext.
  all: try (destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) start (numc + 1) need_pre output_rows_2 Hnext ltac:(lia))
    as [Hcur_next Hcnt_next]; rewrite Hcur_next; exact Hcnt_next).
  all: try (unfold string_length, naive_C_Rules.string_length in *; lia);
       try reflexivity.
  assert (Hcons2 : is_consonant_z_117 (Znth i str_l 0) = true).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnext2 :
    select_scan_state_117 str_l (i + 1) start (numc + 1) need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons2 in Hraw.
    replace (if (start <? 0)%Z then i else start) with start in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    exact Hraw.
  }
  destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) start (numc + 1) need_pre output_rows_2 Hnext2 ltac:(lia))
    as [Hcur_next Hcnt_next].
  rewrite Hcur_next.
  exact Hcnt_next.
Qed.

Lemma proof_of_select_words_entail_wit_8_4 : select_words_entail_wit_8_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  assert (Hcons : is_consonant_z_117 (Znth i str_l 0) = true).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnumc0 : numc = 0).
  {
    unfold select_scan_state_117 in PreH36.
    destruct PreH36 as [_ [_ [Hempty | Hcur]]].
    - destruct Hempty as [_ [_ Hnumc]]; exact Hnumc.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  assert (Hnext :
    select_scan_state_117 str_l (i + 1) i (0 + 1) need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons in Hraw.
    replace (if (start <? 0)%Z then i else start) with i in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    rewrite Hnumc0 in Hraw.
    exact Hraw.
  }
  all: try exact Hnext.
  all: try (destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) i (0 + 1) need_pre output_rows_2 Hnext ltac:(lia))
    as [Hcur_next Hcnt_next]; rewrite Hcur_next; exact Hcnt_next).
  all: try (unfold string_length, naive_C_Rules.string_length in *; lia);
       try reflexivity.
  assert (Hcons2 : is_consonant_z_117 (Znth i str_l 0) = true).
  {
    assert (Hzi : Znth i str_l 0 = Znth i (c_string str_l) 0).
    {
      unfold c_string, naive_C_Rules.c_string.
      rewrite app_Znth1 by (unfold string_length, naive_C_Rules.string_length in *; lia).
      reflexivity.
    }
    rewrite Hzi; exact PreH5.
  }
  assert (Hnumc02 : numc = 0).
  {
    unfold select_scan_state_117 in PreH36.
    destruct PreH36 as [_ [_ [Hempty | Hcur]]].
    - destruct Hempty as [_ [_ Hnumc]]; exact Hnumc.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  assert (Hnext2 :
    select_scan_state_117 str_l (i + 1) i (0 + 1) need_pre output_rows_2).
  {
    assert (Hraw :
      select_scan_state_117 str_l (i + 1)
        (if (start <? 0)%Z then i else start)
        (numc + (if is_consonant_z_117 (Znth i str_l 0) then 1 else 0))
        need_pre output_rows_2).
    {
      eapply (select_scan_state_117_step_nospace
        str_l i start numc need_pre output_rows_2).
      - unfold string_length, naive_C_Rules.string_length in *; lia.
      - exact PreH36.
      - apply is_space_z_117_false_from_neq.
        + unfold string_length, naive_C_Rules.string_length in *; lia.
        + exact PreH8.
    }
    rewrite Hcons2 in Hraw.
    replace (if (start <? 0)%Z then i else start) with i in Hraw
      by (destruct (Z.ltb_spec start 0); lia).
    rewrite Hnumc02 in Hraw.
    exact Hraw.
  }
  destruct (select_scan_state_117_current_nonempty
    str_l (i + 1) i (0 + 1) need_pre output_rows_2 Hnext2 ltac:(lia))
    as [Hcur_next Hcnt_next].
  rewrite Hcur_next.
  exact Hcnt_next.
Qed.

Lemma proof_of_select_words_entail_wit_10 : select_words_entail_wit_10.
Proof.
  constructor; pre_process_default.
  assert (Hstate_n :
    select_scan_state_117 str_l n start numc need_pre output_rows_2)
    by (replace n with i by lia; exact PreH32).
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_117 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_117_empty).
  rewrite CharArray.full_empty.
  select_entailer.
Qed.

Lemma proof_of_select_words_entail_wit_11 : select_words_entail_wit_11.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  select_entailer.
  rewrite word_payload_117_step_offset_c_string by (unfold string_length, naive_C_Rules.string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_select_words_entail_wit_12_1 : select_words_entail_wit_12_1.
Proof.
  constructor; pre_process_default.
  assert (Hi_n : i = n) by lia.
  assert (Hstate_i :
    select_scan_state_117 str_l i (-1) 0 need_pre output_rows_2).
  {
    unfold select_scan_state_117 in PreH29 |- *.
    destruct PreH29 as [Hrange [Hrows [Hempty | Hcur]]].
    - destruct Hempty as [Hcurrent [Hstart Hnumc]].
      split; [exact Hrange|].
      split; [exact Hrows|].
      left; repeat split; try assumption; lia.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  assert (Hstate_n :
    select_scan_state_117 str_l (string_length str_l) (-1) 0 need_pre output_rows_2).
  {
    rewrite <- PreH5.
    rewrite <- Hi_n.
    exact Hstate_i.
  }
  pose proof (select_scan_state_117_final_empty str_l need_pre output_rows_2 Hstate_n) as Hfinal.
  assert (Hnumc0 : numc = 0).
  {
    unfold select_scan_state_117 in PreH29.
    destruct PreH29 as [_ [_ [Hempty | Hcur]]].
    - destruct Hempty as [_ [_ Hnumc]]; exact Hnumc.
    - destruct Hcur as [Hstart_bounds _]; lia.
  }
  Exists output_ptrs_2 output_rows_2.
  rewrite Hfinal.
  select_entailer.
  apply problem_117_spec_z_select_output_rows_117; assumption.
  - rewrite <- Hfinal; lia.
Qed.

Lemma proof_of_select_words_entail_wit_12_2 : select_words_entail_wit_12_2.
Proof.
  constructor; pre_process_default.
  assert (Hi_n : i = n) by lia.
  assert (Hstate_n :
    select_scan_state_117 str_l (string_length str_l) start numc need_pre output_rows_2).
  {
    replace (string_length str_l) with i by lia.
    exact PreH30.
  }
  pose proof (select_scan_state_117_final_not_selected
    str_l start numc need_pre output_rows_2 Hstate_n ltac:(lia) PreH1) as Hfinal.
  Exists output_ptrs_2 output_rows_2.
  rewrite Hfinal.
  select_entailer.
  apply problem_117_spec_z_select_output_rows_117; assumption.
  rewrite <- Hfinal; lia.
Qed.

Lemma proof_of_select_words_entail_wit_12_3 : select_words_entail_wit_12_3.
Proof.
  constructor; pre_process_default.
  assert (Hrow : word_payload_117 str_l start (start + k) = word_payload_117 str_l start n).
  {
    replace (start + k) with n by lia.
    reflexivity.
  }
  rewrite Hrow.
  rewrite <- word_row_117_unfold.
  replace (k + 1) with (Zlength (word_row_117 str_l start n)).
  2:{
    rewrite word_row_117_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite PreH32.
    lia.
  }
  sep_apply (select_words_rows_heap_117_app_single
    output_ptrs_2 output_rows_2 w (word_row_117 str_l start n) ltac:(lia)).
  assert (Hstate_final :
    select_scan_state_117 str_l (string_length str_l) start numc need_pre output_rows_2).
  {
    rewrite <- PreH4.
    exact PreH30.
  }
  pose proof (select_scan_state_117_final_selected
    str_l start numc need_pre output_rows_2 Hstate_final ltac:(lia) PreH19) as Hfinal.
  assert (Hfinal_n :
    output_rows_2 ++ (word_row_117 str_l start n :: nil) =
    select_output_rows_117 str_l need_pre).
  {
    replace n with (string_length str_l) by lia.
    exact Hfinal.
  }
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_117 str_l start n :: nil)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
  - rewrite Hfinal_n.
    apply problem_117_spec_z_select_output_rows_117; assumption.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_select_words_return_wit_1 : select_words_return_wit_1.
Proof.
  constructor; pre_process_default.
  - Exists output_ptrs_2 output_rows_2 data_2.
    entailer!;
      try (rewrite PreH21; apply Zlength_select_output_rows_117_le);
      try (rewrite PreH1; replace (Zlength output_rows_2) with out_size by lia; cancel);
      try lia.
Qed.

Lemma proof_of_select_words_partial_solve_wit_8_pure : select_words_partial_solve_wit_8_pure.
Proof.
  constructor; pre_process_default; entailer!;
    try solve_c_string_char_bound_117; try lia.
Qed.

Lemma proof_of_select_words_partial_solve_wit_9_pure : select_words_partial_solve_wit_9_pure.
Proof.
  constructor; pre_process_default; entailer!;
    try solve_c_string_char_bound_117; try lia.
Qed.
