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
From SimpleC.EE.CAV.ground_truth_p014_all_prefixes Require Import p014_all_prefixes_goal.
From SimpleC.EE.CAV.ground_truth_p014_all_prefixes Require Import p014_all_prefixes_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p014_all_prefixes.
Local Open Scope sac.

Lemma proof_of_all_prefixes_entail_wit_1 : all_prefixes_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 retval).
    rewrite PtrArray.seg_empty.
    unfold store_string.
    entailer!.
    all: try apply prefix_rows_state_14_initial.
    all: try rewrite Zlength_nil; try lia.
    subst retval.
    apply string_length_nonneg.
Qed.

Lemma proof_of_all_prefixes_entail_wit_2 : all_prefixes_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    replace (string_length str_l + 1) with (n + 1) by lia.
    sep_apply_l_atomic (CharArray.full_split_to_seg
      str_pre (i + 1) (n + 1) (c_string str_l)).
    + dump_pre_spatial. unfold string_length in *. lia.
    + sep_apply_l_atomic (CharArray.seg_to_full str_pre 0 (i + 1)
        (sublist 0 (i + 1) (c_string str_l))).
      sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval (i + 2)).
      sep_apply (CharArray.undef_seg_split_to_undef_seg
        retval 0 (i + 1) (i + 2)).
      sep_apply_l_atomic (CharArray.undef_seg_to_undef_full retval 0 (i + 1)).
      replace (str_pre + 0 * sizeof(CHAR)) with str_pre by lia.
      replace (retval + 0 * sizeof(CHAR)) with retval by lia.
      replace (i + 1 - 0) with (i + 1) by lia.
      assert (Hi_str : 0 <= i < string_length str_l) by (subst n; lia).
      rewrite prefix_row_payload_c_string_14 by exact Hi_str.
      entailer!.
      * destruct PreH10 as [Hascii _].
        exact (all_ascii_prefix_row_payload_14 str_l i Hascii Hi_str).
      * exact (Zlength_prefix_row_payload_14 str_l i Hi_str).
      * lia.
Qed.

Lemma proof_of_all_prefixes_entail_wit_3 : all_prefixes_entail_wit_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string.
    sep_apply (CharArray.full_to_seg
      str_pre (i + 1) (prefix_row_payload_14 str_l i)).
    assert (Hi_str : 0 <= i < string_length str_l) by (subst n; lia).
    sep_apply (chararray_adjacent_segs_to_full_14
      str_pre (i + 1) (n + 1)
      (prefix_row_payload_14 str_l i)
      (sublist (i + 1) (n + 1) (c_string str_l))).
    replace (n + 1) with (string_length str_l + 1) by lia.
    entailer!.
    + replace (string_length str_l + 1) with (n + 1) by lia.
      pose proof (prefix_row_payload_suffix_c_string_14 str_l i n ltac:(lia) PreH4)
        as Hsuffix.
      rewrite <- Hsuffix at 2.
      entailer!.
    + lia.
Qed.

Lemma proof_of_all_prefixes_entail_wit_4 : all_prefixes_entail_wit_4.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string, prefix_row_14.
    replace ((i + 1) + 1) with (i + 2) by lia.
    replace ((prefix_row_payload_14 str_l i ++ 0 :: nil)%list)
      with (c_string (prefix_row_payload_14 str_l i)) by reflexivity.
    rewrite CharArray.undef_seg_empty.
    entailer!.
Qed.

Lemma proof_of_all_prefixes_entail_wit_5 : all_prefixes_entail_wit_5.
Proof.
  constructor.
  - pre_process_default.
    Exists ((output_ptrs_2 ++ (cur :: nil))%list)
      ((output_rows_2 ++ (prefix_row_14 str_l i :: nil))%list).
    replace (i + 2) with (Zlength (prefix_row_14 str_l i)).
    2: {
      unfold prefix_row_14, naive_C_Rules.c_string.
      rewrite Zlength_app_cons.
      assert (Hi_str : 0 <= i < string_length str_l) by lia.
      pose proof (Zlength_prefix_row_payload_14 str_l i Hi_str) as Hpayload_len.
      rewrite Hpayload_len.
      lia.
    }
    assert (Hrows_len : Zlength output_ptrs_2 = Zlength output_rows_2) by lia.
    sep_apply (prefix_rows_heap_14_app_single
      output_ptrs_2 output_rows_2 cur (prefix_row_14 str_l i) Hrows_len).
    unfold store_string.
      entailer!.
      * rewrite Zlength_app_cons. lia.
      * rewrite Zlength_app_cons. lia.
      * assert (Hi_str : 0 <= i < string_length str_l) by lia.
        exact (prefix_rows_state_14_step str_l i output_rows_2 PreH13 Hi_str).
Qed.

Lemma proof_of_all_prefixes_entail_wit_7 : all_prefixes_entail_wit_7.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    replace i with n by lia.
    rewrite PtrArray.undef_seg_empty.
    entailer!.
    assert (Hstate_final :
      prefix_rows_state_14 str_l (string_length str_l) output_rows_2).
    {
      replace (string_length str_l) with i by lia.
      exact PreH11.
    }
    exact (prefix_rows_14_spec str_l output_rows_2 Hstate_final).
    replace n with i by lia.
    exact PreH11.
Qed.

Lemma proof_of_all_prefixes_return_wit_1 : all_prefixes_return_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2 data_2.
    replace (string_length str_l) with n by lia.
    entailer!.
Qed.

Lemma proof_of_all_prefixes_partial_solve_wit_3_pure_split_goal_1 : all_prefixes_partial_solve_wit_3_pure_split_goal_1.
Proof.
  pre_process_default.
  entailer!.
  subst retval.
  apply string_length_nonneg.
Qed.

Lemma proof_of_all_prefixes_partial_solve_wit_3_pure : all_prefixes_partial_solve_wit_3_pure.
Proof.
  constructor.
  - pre_process_default.
    entailer!.
    subst retval.
    apply string_length_nonneg.
Qed.
