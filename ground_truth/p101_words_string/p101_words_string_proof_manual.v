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
From SimpleC.EE.CAV.ground_truth_p101_words_string Require Import p101_words_string_goal.
From SimpleC.EE.CAV.ground_truth_p101_words_string Require Import p101_words_string_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p101_words_string.
Local Open Scope sac.

Ltac solve_c_string_char_bound :=
  match goal with
  | Hvalid : valid_string ?s |- 0 <= Znth ?i (c_string ?s) 0 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  | Hvalid : valid_string ?s |- Znth ?i (c_string ?s) 0 <= 127 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  end.

Ltac solve_word_payload_goal :=
  match goal with
  | Hstate : split_scan_state_101 ?s ?i ?start ?rows
      |- split_scan_current_101 ?s ?i = word_payload_101 ?s ?start ?i =>
      apply (split_scan_state_101_current_nonempty s i start rows Hstate); lia
  | |- Zlength (word_payload_101 ?s ?start ?stop) = ?stop - ?start =>
      apply Zlength_word_payload_101; unfold string_length in *; lia
  end.

Ltac solve_delim_goal :=
  match goal with
  | H : Znth ?i (c_string ?s) 0 = 32
      |- is_delim_z_101 (Znth ?i (c_string ?s) 0) = true =>
      unfold is_delim_z_101; rewrite H; reflexivity
  | H : Znth ?i (c_string ?s) 0 = 44
      |- is_delim_z_101 (Znth ?i (c_string ?s) 0) = true =>
      unfold is_delim_z_101; rewrite H; reflexivity
  end.

Ltac words_entailer :=
  entailer!;
  try solve_c_string_char_bound;
  try solve_word_payload_goal;
  try solve_delim_goal;
  try lia.

Lemma proof_of_words_string_entail_wit_1 : words_string_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  Exists (@nil Z) (@nil (list Z)).
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 (retval + 1)).
  rewrite PtrArray.seg_empty.
  unfold store_string.
  entailer!.
  - apply split_scan_state_101_initial.
  - subst retval; apply string_length_nonneg.
Qed.

Lemma proof_of_words_string_entail_wit_2_1 : words_string_entail_wit_2_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_2_2 : words_string_entail_wit_2_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_3 : words_string_entail_wit_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  rewrite word_payload_101_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_4 : words_string_entail_wit_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  rewrite CharArray.undef_seg_empty.
  words_entailer.
  rewrite word_row_101_unfold.
  replace (start + k) with i by lia.
  replace (k + 1) with (len + 1) by lia.
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_5 : words_string_entail_wit_5.
Proof.
  constructor; pre_process_default.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_101 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_101 str_l start i) = len + 1).
  {
    rewrite word_row_101_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_101 by (unfold string_length in *; lia).
    lia.
  }
  replace (len + 1) with (Zlength (word_row_101 str_l start i)) by lia.
  sep_apply (words_rows_heap_101_app_single
    output_ptrs_2 output_rows_2 w (word_row_101 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  words_entailer.
  apply split_scan_state_101_step_delim_nonempty.
  - exact PreH25.
  - lia.
  - rewrite PreH16 in PreH17.
    rewrite c_string_Znth_before_101 in PreH17 by (unfold string_length in *; lia).
    exact PreH17.
  - unfold string_length in *; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_words_string_entail_wit_6_1 : words_string_entail_wit_6_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  replace start with (-1) by lia.
  apply split_scan_state_101_step_delim_empty.
  - replace start with (-1) in PreH25 by lia; exact PreH25.
  - apply is_delim_z_101_true_44; unfold string_length in *; lia || exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_6_2 : words_string_entail_wit_6_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  replace start with (-1) by lia.
  apply split_scan_state_101_step_delim_empty.
  - replace start with (-1) in PreH24 by lia; exact PreH24.
  - apply is_delim_z_101_true_32; unfold string_length in *; lia || exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_7_1 : words_string_entail_wit_7_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  apply split_scan_state_101_step_nondelim_continue.
  - exact PreH25.
  - lia.
  - apply is_delim_z_101_false_from_neq.
    + unfold string_length in *; lia.
    + exact PreH3.
    + exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_7_2 : words_string_entail_wit_7_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  apply split_scan_state_101_step_nondelim_start.
  - replace start with (-1) in PreH25 by lia; exact PreH25.
  - apply is_delim_z_101_false_from_neq.
    + unfold string_length in *; lia.
    + exact PreH3.
    + exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_9 : words_string_entail_wit_9.
Proof.
  constructor; pre_process_default.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_10 : words_string_entail_wit_10.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  rewrite word_payload_101_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_11_1 : words_string_entail_wit_11_1.
Proof.
  constructor; pre_process_default.
  replace i with n in * by lia.
  replace start with (-1) in * by lia.
  assert (Hfinal : output_rows_2 = words_output_rows_101 str_l).
  {
    apply split_scan_state_101_final_empty.
    replace (Zlength str_l) with n by (unfold string_length in *; lia).
    exact PreH23.
  }
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!.
  - rewrite Hfinal.
    apply problem_101_spec_z_words_output_rows_101.
    exact PreH19.
Qed.

Lemma proof_of_words_string_entail_wit_11_2 : words_string_entail_wit_11_2.
Proof.
  constructor; pre_process_default.
  replace k with len in * by lia.
  replace (start + len) with n in * by lia.
  assert (Hrow_len : Zlength (word_row_101 str_l start n) = len + 1).
  {
    rewrite word_row_101_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_101 by (unfold string_length in *; lia).
    lia.
  }
  assert (Hfinal :
    output_rows_2 ++ (word_row_101 str_l start n :: nil) =
    words_output_rows_101 str_l).
  {
    replace n with (Zlength str_l) by (unfold string_length in *; lia).
    apply split_scan_state_101_final_nonempty.
    - replace n with (Zlength str_l) in PreH24 by (unfold string_length in *; lia).
      exact PreH24.
    - unfold string_length in *; lia.
  }
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_101 str_l start n :: nil)).
  rewrite <- word_row_101_unfold.
  replace (len + 1) with (Zlength (word_row_101 str_l start n)) by lia.
  sep_apply (words_rows_heap_101_app_single
    output_ptrs_2 output_rows_2 w (word_row_101 str_l start n) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
  - rewrite Hfinal.
    apply problem_101_spec_z_words_output_rows_101.
    exact PreH20.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
       try (rewrite Hfinal; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
       try (rewrite <- Hfinal; entailer!).
Qed.

Lemma proof_of_words_string_return_wit_1 : words_string_return_wit_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2 data_2.
  unfold store_string.
  replace (Zlength output_rows_2) with out_size by lia.
  replace (string_length str_l + 1) with (n + 1) by lia.
  entailer!.
  - rewrite PreH8.
    rewrite PreH16.
    replace (n + 1) with (Zlength str_l + 1) by (unfold string_length in *; lia).
    apply Zlength_words_output_rows_101_le.
Qed.
