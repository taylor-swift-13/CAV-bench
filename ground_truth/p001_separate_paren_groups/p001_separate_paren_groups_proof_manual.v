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
From SimpleC.EE.CAV.ground_truth_p001_separate_paren_groups Require Import p001_separate_paren_groups_goal.
From SimpleC.EE.CAV.ground_truth_p001_separate_paren_groups Require Import p001_separate_paren_groups_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p001_separate_paren_groups.
Local Open Scope sac.

Ltac solve_c_string_char_bound_1 :=
  match goal with
  | Hvalid : valid_string ?s |- 0 <= Znth ?i (c_string ?s) 0 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  | Hvalid : valid_string ?s |- Znth ?i (c_string ?s) 0 <= 127 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  end.

Ltac paren_entailer :=
  entailer!;
  try solve_c_string_char_bound_1;
  try lia.

Lemma proof_of_separate_paren_groups_entail_wit_1 : separate_paren_groups_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  subst retval.
  Exists (@nil Z) (@nil (list Z)).
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 (string_length str_l + 1)).
  rewrite PtrArray.seg_empty.
  change (paren_rows_heap_1 (@nil Z) (@nil (list Z))) with emp.
  unfold store_string.
  entailer!.
  - rewrite Zlength_nil.
    cancel.
  - apply paren_scan_state_1_initial.
  - apply string_length_nonneg.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_2_1 : separate_paren_groups_entail_wit_2_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - eapply paren_scan_state_1_step_open_continue; eauto.
    unfold string_length in *; lia.
  - eapply paren_scan_state_1_nonzero_start; eauto.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_2_2 : separate_paren_groups_entail_wit_2_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hstart0 : start = -1) by
    (eapply paren_scan_state_1_level0_start; rewrite <- PreH1; exact PreH27).
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - rewrite Hstart0 in PreH27.
    rewrite PreH1 in PreH27.
    replace (level + 1) with 1 by lia.
    eapply paren_scan_state_1_step_open_start; eauto.
    unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_3 : separate_paren_groups_entail_wit_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hlevel1 : level = 1) by lia.
  rewrite Hlevel1 in PreH30.
  pose proof (paren_scan_state_1_nonzero_start _ _ _ _ _ PreH30 ltac:(lia)) as Hstart_nonneg.
  replace (start + 0) with start by lia.
  rewrite paren_payload_1_empty.
  rewrite CharArray.full_empty.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval (((i - start) + 1) + 1)).
  unfold store_string.
  paren_entailer.
  - rewrite PreH14, PreH9.
    cancel.
  - rewrite Zlength_paren_payload_1; unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_4 : separate_paren_groups_entail_wit_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  rewrite <- paren_payload_1_step_offset_c_string by (unfold string_length in *; lia).
  unfold store_string.
  paren_entailer.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_5 : separate_paren_groups_entail_wit_5.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  replace k with len by lia.
  replace (start + len) with (i + 1) by lia.
  rewrite paren_row_1_unfold.
  rewrite CharArray.undef_seg_empty.
  unfold store_string.
  paren_entailer.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_6 : separate_paren_groups_entail_wit_6.
Proof.
  constructor; pre_process_default.
  Exists (app output_ptrs_2 (cons row nil))
    (app output_rows_2 (cons (paren_row_1 str_l start (i + 1)) nil)).
  assert (Hpayload_len : Zlength (paren_payload_1 str_l start (i + 1)) = len) by
    (rewrite Zlength_paren_payload_1 by (unfold string_length in *; lia); lia).
  assert (Hrow_len : Zlength (paren_row_1 str_l start (i + 1)) = len + 1) by
    (rewrite paren_row_1_unfold, Zlength_app, Hpayload_len,
       Zlength_cons, Zlength_nil; lia).
  replace (len + 1) with (Zlength (paren_row_1 str_l start (i + 1))) by lia.
  sep_apply (paren_rows_heap_1_app_single output_ptrs_2 output_rows_2 row
    (paren_row_1 str_l start (i + 1)) ltac:(lia)).
  rewrite PreH15.
  unfold store_string.
  paren_entailer.
  - eapply paren_scan_state_1_step_close_finish.
    + exact PreH25.
    + lia.
    + unfold naive_C_Rules.c_string, c_string in *; lia.
    + unfold string_length in *; lia.
  - rewrite Zlength_app, PreH12.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, PreH11.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_7 : separate_paren_groups_entail_wit_7.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hlevel_pos : 0 < level).
  {
    unfold paren_safe_input_1 in PreH25.
    destruct PreH25 as [PreH25 _].
    specialize (PreH25 i ltac:(unfold string_length in *; lia) PreH2).
    unfold paren_scan_state_1 in PreH28.
    lia.
  }
  unfold store_string.
  paren_entailer.
  - rewrite PreH12, PreH7.
    cancel.
  - eapply paren_scan_state_1_step_close_continue; eauto.
    unfold string_length in *; lia.
  - eapply paren_scan_state_1_nonzero_start; eauto.
    intro Hzero; subst level.
    unfold paren_safe_input_1 in PreH25.
    destruct PreH25 as [PreH25 _].
    specialize (PreH25 i ltac:(unfold string_length in *; lia) PreH2).
    unfold paren_scan_state_1 in PreH28.
    lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_8 : separate_paren_groups_entail_wit_8.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  pose proof (valid_paren_input_1_space str_l i PreH23
    ltac:(unfold string_length in *; lia) PreH1 PreH2) as Hspace.
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - eapply paren_scan_state_1_step_space; eauto.
    unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_1 : separate_paren_groups_entail_wit_9_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_2 : separate_paren_groups_entail_wit_9_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH9, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_3 : separate_paren_groups_entail_wit_9_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_4 : separate_paren_groups_entail_wit_9_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_10 : separate_paren_groups_entail_wit_10.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hi_done : i = Zlength str_l) by (unfold string_length in *; lia).
  pose proof PreH22 as Hsafe_all.
  unfold paren_safe_input_1 in PreH22.
  destruct PreH22 as [_ [Hlevel_done [Hstart_done Hspec]]].
  assert (Hrows_done : output_rows_2 = paren_output_rows_1 str_l).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [Hrows _]].
    unfold paren_output_rows_1.
    rewrite Hrows, Hi_done.
    reflexivity.
  }
  assert (Hlevel0 : level = 0).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [_ [Hlev _]]].
    rewrite Hlev, Hi_done.
    exact Hlevel_done.
  }
  assert (Hstart0 : start = -1).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [_ [_ [Hstart _]]]].
    rewrite Hstart, Hi_done.
    exact Hstart_done.
  }
  unfold store_string.
  paren_entailer.
  - rewrite Hrows_done.
    exact Hspec.
Qed.
