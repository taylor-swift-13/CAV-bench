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
From SimpleC.EE.CAV.ground_truth_p158_find_max Require Import p158_find_max_goal.
From SimpleC.EE.CAV.ground_truth_p158_find_max Require Import p158_find_max_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p158_find_max.
Local Open Scope sac.

Lemma proof_of_find_max_entail_wit_1 : find_max_entail_wit_1.
Proof.
  pre_process_default.
  unfold zeros; simpl.
  rewrite IntArray.seg_empty.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_2 : find_max_entail_wit_2.
Proof.
  pre_process_default.
  rewrite zeros_snoc_158 by lia.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_3 : find_max_entail_wit_3.
Proof.
  pre_process_default.
  subst.
  Exists (zeros 128).
  replace k with 128 by lia.
  rewrite (IntArray.undef_seg_empty ( &( "seen" ) ) 128).
  sep_apply (IntArray.seg_to_full ( &( "seen" ) ) 0 128 (zeros 128)).
  replace ((&( "seen" ) + 0 * sizeof(INT))) with (&( "seen" )) by lia.
  replace (128 - 0) with 128 by lia.
  entailer!.
  apply best_prefix_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_4 : find_max_entail_wit_4.
Proof.
  pre_process_default.
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i words_pre i words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth i rows ?d] => rewrite (Znth_indep rows i nil d) by lia
    end.
    entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_5 : find_max_entail_wit_5.
Proof.
  pre_process_default.
  Exists row_ptr_2 seen_l_2.
  entailer!.
  apply reset_prefix_state_158_initial; auto.
Qed.

Lemma proof_of_find_max_entail_wit_6 : find_max_entail_wit_6.
Proof.
  pre_process_default.
  Exists row_ptr_2 (replace_Znth k 0 seen_l_2).
  entailer!.
  - apply reset_prefix_state_158_step; auto; lia.
  - rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_7 : find_max_entail_wit_7.
Proof.
  pre_process_default.
  assert (seen_l = zeros 128) as ->.
  { eapply reset_prefix_state_158_full_zero; eauto; lia. }
  Exists row_ptr_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_8 : find_max_entail_wit_8.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia)) as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [_ [_ Hlen]]]]].
  rewrite Hrow.
  unfold store_string.
  rewrite row_payload_c_string_158.
  rewrite c_string_Zlength_158.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_9 : find_max_entail_wit_9.
Proof.
  pre_process_default.
  Exists (zeros 128).
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_row rows words_size_pre i Hwf ltac:(lia))
        as Hrow_info
  end.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (0 <= retval) by (rewrite PreH1; unfold string_length; apply Zlength_nonneg).
  unfold store_string.
  rewrite <- Hrow.
  rewrite <- Hlen.
  entailer!.
  apply count_scan_state_158_initial.
Qed.

Lemma proof_of_find_max_entail_wit_10 : find_max_entail_wit_10.
Proof.
  pre_process_default.
  match goal with
  | Hwf : rows_well_formed_158 rows words_size_pre |- _ =>
      pose proof (rows_well_formed_158_char_bound rows words_size_pre i j
        Hwf ltac:(lia) ltac:(lia)) as Hchar_bound
  end.
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_11_1 : find_max_entail_wit_11_1.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  assert (Hnew_state :
    count_scan_state_158
      (Znth i rows nil) (j + 1) (replace_Znth ch 1 seen_l_2) (unique + 1)).
  { eapply count_scan_state_158_step_new; eauto; lia. }
  assert (Hunique_bound : unique + 1 <= 128).
  {
    unfold count_scan_state_158 in Hnew_state.
    destruct Hnew_state as [_ [_ [_ Huniq_new]]].
    rewrite Huniq_new.
    apply Hprefix. rewrite <- PreH18. lia.
  }
  Exists (replace_Znth ch 1 seen_l_2).
  entailer!.
  rewrite Zlength_replace_Znth; lia.
Qed.

Lemma proof_of_find_max_entail_wit_11_2 : find_max_entail_wit_11_2.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [Hrow [Hvalid [Hlt [Hprefix [Hbound Hlen]]]]].
  assert (Hch_payload : ch = Znth j (row_payload_z_158 (Znth i rows nil)) 0).
  {
    rewrite Hrow in PreH11.
    rewrite string_lib.c_string_Znth_inside in PreH11 by (rewrite <- PreH18; lia).
    exact PreH11.
  }
  Exists seen_l_2.
  entailer!.
  eapply count_scan_state_158_step_seen; eauto; lia.
Qed.

Lemma proof_of_find_max_entail_wit_12 : find_max_entail_wit_12.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH17. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH26.
    eapply count_scan_state_158_complete; exact PreH26.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
    as Hcur_info.
  pose proof (rows_well_formed_158_row rows words_size_pre best_idx PreH23 ltac:(lia))
    as Hbest_info.
  destruct Hcur_info as [Hcur_row [Hcur_valid [Hcur_lt [_ [_ Hcur_len]]]]].
  destruct Hbest_info as [Hbest_row [Hbest_valid [Hbest_lt [_ [_ Hbest_len]]]]].
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_split_two_158
      words_pre words_size_pre i best_idx row_ptr rows ltac:(lia) ltac:(lia) PreH1).
  Intros best_ptr.
  Exists best_ptr seen_l_2.
  rewrite Hcur_row in Hcur_len.
  rewrite Hbest_row in Hbest_len.
  rewrite Hcur_row.
  rewrite Hbest_row.
  rewrite !row_payload_c_string_158 in *.
  unfold store_string.
  rewrite <- Hcur_len, <- Hbest_len.
  entailer!.
  rewrite <- Hcur_row.
  exact Hunique_final.
Qed.

Lemma proof_of_find_max_entail_wit_15_1 : find_max_entail_wit_15_1.
Proof.
  pre_process_default.
  - assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
    { rewrite <- PreH17. lia. }
    assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
    {
      rewrite Hj_len in PreH26.
      eapply count_scan_state_158_complete; exact PreH26.
    }
    pose proof (proj1 PreH23) as Hrows_len.
    pose proof (rows_well_formed_158_row rows words_size_pre i PreH23 ltac:(lia))
      as Hrow_info.
    destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
    assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
    {
      eapply best_prefix_state_158_step_keep
        with (curu := unique); eauto; try lia.
      intros _.
      subst best_idx.
      apply string_le_refl_158.
    }
    sep_apply_l_atomic
      (char_ptr_array2_missing_i_merge_full_158
        words_pre words_size_pre i row_ptr rows ltac:(lia)).
    Exists seen_l_2.
    entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_2 : find_max_entail_wit_15_2.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH16. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH25.
    eapply count_scan_state_158_complete; exact PreH25.
  }
  pose proof (proj1 PreH22) as Hrows_len.
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH22 ltac:(lia))
    as Hrow_info.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique); eauto; try lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
  Unshelve.
  all: try lia; try entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_3 : find_max_entail_wit_15_3.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Hstep : best_prefix_state_158 rows (i + 1) best_idx maxu).
  {
    eapply best_prefix_state_158_step_keep
      with (curu := unique).
    - exact PreH19.
    - lia.
    - exact PreH11.
    - lia.
    - intros _.
      subst unique.
      eapply strcmp_result_ge_string_le_158; eauto; lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_4 : find_max_entail_wit_15_4.
Proof.
  right.
  pre_process_default.
  pose proof (proj1 PreH17) as Hrows_len.
  assert (Htie :
    string_le
      (row_string_z_158 (Znth i rows nil))
      (row_string_z_158 (Znth best_idx rows nil))).
  {
    eapply strcmp_result_lt_string_le_158; eauto; lia.
  }
  assert (Hstep : best_prefix_state_158 rows (i + 1) i maxu).
  {
    assert (Hstep_unique : best_prefix_state_158 rows (i + 1) i unique).
    {
      eapply best_prefix_state_158_step_update_tie
        with (best_idx := best_idx) (maxu := maxu); eauto; try lia.
    }
    rewrite PreH12 in Hstep_unique.
    exact Hstep_unique.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_two_merge_full_cstring_158
      words_pre words_size_pre i row_ptr best_idx best_ptr rows
      PreH17 ltac:(lia) ltac:(lia) ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_15_5 : find_max_entail_wit_15_5.
Proof.
  pre_process_default.
  assert (Hj_len : j = string_lib.string_length (row_payload_z_158 (Znth i rows nil))).
  { rewrite <- PreH15. lia. }
  assert (Hunique_final : unique = row_unique_count_z_158 (Znth i rows nil)).
  {
    rewrite Hj_len in PreH24.
    eapply count_scan_state_158_complete; exact PreH24.
  }
  pose proof (rows_well_formed_158_row rows words_size_pre i PreH21 ltac:(lia))
    as Hrow_info.
  pose proof (proj1 PreH21) as Hrows_len.
  destruct Hrow_info as [_ [_ [Hlen_lt [_ [_ _]]]]].
  assert (Hstep : best_prefix_state_158 rows (i + 1) i unique).
  {
    eapply best_prefix_state_158_step_update_strict
      with (best_idx := best_idx) (maxu := maxu).
    - exact PreH23.
    - lia.
    - exact Hunique_final.
    - lia.
  }
  sep_apply_l_atomic
    (char_ptr_array2_missing_i_merge_full_158
      words_pre words_size_pre i row_ptr rows ltac:(lia)).
  Exists seen_l_2.
  entailer!.
Qed.

Lemma proof_of_find_max_entail_wit_17 : find_max_entail_wit_17.
Proof.
  pre_process_default.
  assert (Hi_end : i = words_size_pre) by lia.
  subst i.
  assert (Hspec : problem_158_spec_z rows best_idx).
  {
    eapply best_prefix_state_158_final_spec; eauto; lia.
  }
  prop_apply (CharPtrArray2.full_Zlength words_pre words_size_pre rows).
  Intros.
  sep_apply_l_atomic
    (CharPtrArray2.full_split_to_missing_i
      words_pre best_idx words_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr seen_l_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    repeat match goal with
    | |- context [Znth best_idx rows ?d] =>
        rewrite (Znth_indep rows best_idx nil d) by lia
    end.
    entailer!.
Qed.
