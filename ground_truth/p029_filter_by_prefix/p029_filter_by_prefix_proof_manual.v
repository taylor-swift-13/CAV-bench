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
From SimpleC.EE.CAV.ground_truth_p029_filter_by_prefix Require Import p029_filter_by_prefix_goal.
From SimpleC.EE.CAV.ground_truth_p029_filter_by_prefix Require Import p029_filter_by_prefix_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p029_filter_by_prefix.
Local Open Scope sac.

Ltac c29_row_facts Hwf :=
  let Hrow := fresh "Hrow" in
  match goal with
  | r : list (list Z), n : Z |- _ =>
      match goal with
      | |- context[Znth ?idx r nil] =>
          pose proof (rows_well_formed_29_row r n idx Hwf ltac:(lia)) as Hrow;
          simpl in Hrow;
          destruct Hrow as [? [? [? ?]]]
      end
  end.

Lemma proof_of_filter_by_prefix_entail_wit_1 : filter_by_prefix_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 strings_size_pre).
    rewrite PtrArray.seg_empty.
    unfold store_string.
    entailer!.
    apply filter_prefix_state_29_initial.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_2 : filter_by_prefix_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    c29_row_facts PreH11.
    sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i strings_pre i strings_size_pre rows).
    + dump_pre_spatial. lia.
    + Intros row_ptr.
      Exists row_ptr output_ptrs_2 output_rows_2.
      unfold StorePtrAsElement.storeA.
      rewrite sizeof_ptr.
      change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
        with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
      unfold store_string.
      rewrite H.
      repeat rewrite row_payload_c_string_29.
      repeat rewrite c_string_Zlength_29.
      entailer!.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_4 : filter_by_prefix_entail_wit_4.
Proof.
  constructor.
  - pre_process_default.
    c29_row_facts PreH14.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string.
    rewrite H.
    repeat rewrite row_payload_c_string_29.
    repeat rewrite c_string_Zlength_29.
    entailer!.
    repeat rewrite row_payload_c_string_29.
    eapply strncmp_result_prefix_match_29 with (n := plen) (ret := retval); eauto;
      repeat rewrite row_payload_c_string_29; eauto.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_5 : filter_by_prefix_entail_wit_5.
Proof.
  constructor.
  - pre_process_default.
    Exists (output_ptrs_2 ++ row_ptr :: nil) (output_rows_2 ++ Znth i rows nil :: nil).
    rewrite sizeof_ptr.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    unfold store_string.
    entailer!.
    -- eapply filter_prefix_prefix_29_step_add; eauto.
       destruct PreH13 as [Hrows_len _].
       rewrite Hrows_len.
       lia.
    -- rewrite Zlength_app_cons. lia.
    -- rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_6 : filter_by_prefix_entail_wit_6.
Proof.
  constructor.
  - pre_process_default.
    c29_row_facts PreH14.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string.
    rewrite H.
    repeat rewrite row_payload_c_string_29.
    repeat rewrite c_string_Zlength_29.
    entailer!.
    repeat rewrite row_payload_c_string_29.
    eapply strncmp_result_prefix_nomatch_29 with (n := plen) (ret := retval); eauto;
      repeat rewrite row_payload_c_string_29; eauto.
Qed.

Lemma proof_of_filter_by_prefix_entail_wit_7 : filter_by_prefix_entail_wit_7.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    rewrite sizeof_ptr.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
    eapply filter_prefix_prefix_29_step_skip; eauto.
    destruct PreH11 as [Hrows_len _].
    rewrite Hrows_len.
    lia.
Qed.

Lemma proof_of_filter_by_prefix_return_wit_1 : filter_by_prefix_return_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists data_2 output_ptrs_2 output_rows_2 output_size_2.
    entailer!.
    eapply problem_29_spec_z_of_filter_state.
    replace i with strings_size_pre in PreH15 by lia.
    destruct PreH11 as [Hrows_len _].
    rewrite Hrows_len.
    exact PreH15.
Qed.

Lemma proof_of_filter_by_prefix_partial_solve_wit_4_pure_split_goal_1 : filter_by_prefix_partial_solve_wit_4_pure_split_goal_1.
Proof.
  pre_process_default.
  entailer!.
  subst plen.
  apply string_length_nonneg.
Qed.

Lemma proof_of_filter_by_prefix_partial_solve_wit_4_pure : filter_by_prefix_partial_solve_wit_4_pure.
Proof.
  right.
  apply proof_of_filter_by_prefix_partial_solve_wit_4_pure_split_goal_1.
Qed.
