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
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p149_sorted_list_sum Require Import p149_sorted_list_sum_goal.
From SimpleC.EE.CAV.ground_truth_p149_sorted_list_sum Require Import p149_sorted_list_sum_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p149_sorted_list_sum.
Local Open Scope sac.

#[local] Hint Resolve rows_well_formed_149_row : core.
#[local] Hint Resolve filter_even_step_take_149_intro : core.
#[local] Hint Resolve filter_even_step_keep_149_intro : core.
#[local] Hint Resolve problem_149_spec_z_of_sorted_prefix_intro : core.

Ltac solve_vc_149 :=
  pre_process;
  try unfold rows_length_149, ptrs_length_149 in *;
  entailer!;
  eauto;
  try lia.

Lemma charptr_missing_i_merge_current_149 : forall x i n row_ptr rows row,
  0 <= i < n ->
  StorePtrAsElement.storeA x i row_ptr **
  CharPtrArray2.missing_i x n i row_ptr rows **
  CharArray.full row_ptr (Zlength row) row |--
    CharPtrArray2.full x n (replace_Znth i row rows).
Proof.
  intros.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    x i n row_ptr rows row H) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr (Zlength row) row)
    with (CharArray.full row_ptr (Zlength row) row) in Hmerge.
  unfold StorePtrAsElement.storeA.
  sepcon_lift (CharArray.full row_ptr (Zlength row) row).
  sepcon_lift (((x + i * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  apply derivable1_refl.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_1 : sorted_list_sum_entail_wit_1.
Proof.
  unfold sorted_list_sum_entail_wit_1.
  left.
  intros.
  Exists (@nil Z) (@nil (list Z)).
  unfold filter_even_state_149, filter_even_prefix_149.
  simpl.
  entailer!.
  - rewrite PtrArray.seg_empty.
    entailer!.
  - apply Zlength_nonneg.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_2 : sorted_list_sum_entail_wit_2.
Proof.
  unfold sorted_list_sum_entail_wit_2.
  left.
  intros.
  pose proof (rows_well_formed_149_row rows lst_size_pre i PreH10 ltac:(lia))
    as Hrow.
  simpl in Hrow.
  destruct Hrow as [Hrow_eq [Hvalid Hlen]].
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i lst_pre i lst_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr output_ptrs_2 output_rows_2.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
    unfold store_string.
    rewrite Hrow_eq.
    rewrite row_payload_c_string_payload_149.
    rewrite c_string_Zlength_149.
    entailer!.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_4 : sorted_list_sum_entail_wit_4.
Proof.
  unfold sorted_list_sum_entail_wit_4.
  left.
  intros.
  assert (Hirows : 0 <= i < Zlength rows).
  {
    destruct PreH12 as [Hlen_rows _].
    lia.
  }
  assert (Heven : even_row_z_149 (Znth i rows nil) = true).
  {
    unfold even_row_z_149, row_len_z_149.
    apply Z_even_true_of_rem2_149.
    - unfold string_lib.string_length.
      apply Zlength_nonneg.
    - rewrite <- PreH2.
      exact PreH1.
  }
  Exists (output_rows_2 ++ cons (Znth i rows nil) nil) output_ptrs_2 output_rows_2.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_5 : sorted_list_sum_entail_wit_5.
Proof.
  unfold sorted_list_sum_entail_wit_5.
  left.
  intros.
  Exists (app output_ptrs_2 (cons row_ptr nil)) output_rows_next.
  rewrite sizeof_ptr.
  pose proof (charptr_missing_i_merge_current_149
    lst_pre i lst_size_pre row_ptr rows (Znth i rows nil) ltac:(lia)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite <- c_string_Zlength_149.
  rewrite (row_payload_c_string_149 rows lst_size_pre i PreH11 ltac:(lia)).
  sepcon_lift (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows).
  sepcon_lift (((lst_pre + i * 4)) # Ptr |-> row_ptr).
  sep_apply_l_atomic Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  destruct PreH14 as [Hnext_eq Hnext_state].
  entailer!.
  all: try rewrite Hnext_eq; try rewrite Zlength_app_cons; try lia; try exact Hnext_state.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_6 : sorted_list_sum_entail_wit_6.
Proof.
  unfold sorted_list_sum_entail_wit_6.
  left.
  intros.
  assert (Hirows : 0 <= i < Zlength rows).
  {
    destruct PreH12 as [Hlen_rows _].
    lia.
  }
  assert (Hodd : even_row_z_149 (Znth i rows nil) = false).
  {
    unfold even_row_z_149, row_len_z_149.
    apply Z_even_false_of_rem2_nonzero_149.
    - unfold string_lib.string_length.
      apply Zlength_nonneg.
    - rewrite <- PreH2.
      exact PreH1.
  }
  Exists output_ptrs_2 output_rows_2.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_7 : sorted_list_sum_entail_wit_7.
Proof.
  unfold sorted_list_sum_entail_wit_7.
  left.
  intros.
  Exists output_ptrs_2 output_rows_2.
  rewrite sizeof_ptr.
  pose proof (charptr_missing_i_merge_current_149
    lst_pre i lst_size_pre row_ptr rows (Znth i rows nil) ltac:(lia)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  unfold store_string.
  rewrite <- c_string_Zlength_149.
  rewrite (row_payload_c_string_149 rows lst_size_pre i PreH10 ltac:(lia)).
  sepcon_lift (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows).
  sepcon_lift (((lst_pre + i * 4)) # Ptr |-> row_ptr).
  sep_apply_l_atomic Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_entail_wit_9 : sorted_list_sum_entail_wit_9.
Proof.
  unfold sorted_list_sum_entail_wit_9.
  left.
  intros.
  Exists sorted_ptrs_2 sorted_rows_2 output_rows.
  unfold rows_length_149, ptrs_length_149 in *.
  assert (Hi_eq : i = lst_size_pre) by lia.
  subst i.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_return_wit_1 : sorted_list_sum_return_wit_1.
Proof.
  unfold sorted_list_sum_return_wit_1.
  left.
  intros.
  assert (Hspec : problem_149_spec_z rows sorted_rows).
  {
    unfold problem_149_spec_z_of_sorted_prefix in PreH13.
    pose proof (proj1 PreH8) as Hrows_len.
    rewrite Hrows_len in PreH13.
    exact (PreH13 PreH12 PreH11).
  }
  Exists sorted_ptrs sorted_rows output_size_2 data_2.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_partial_solve_wit_5_pure_split_goal_1 : sorted_list_sum_partial_solve_wit_5_pure_split_goal_1.
Proof.
  unfold sorted_list_sum_partial_solve_wit_5_pure_split_goal_1.
  intros.
  entailer!.
  destruct PreH18 as [_ [Hsize_lt _]].
  exact Hsize_lt.
Qed.

Lemma proof_of_sorted_list_sum_partial_solve_wit_5_pure_split_goal_2 : sorted_list_sum_partial_solve_wit_5_pure_split_goal_2.
Proof.
  unfold sorted_list_sum_partial_solve_wit_5_pure_split_goal_2.
  intros.
  entailer!.
  unfold rows_length_149.
  destruct PreH20 as [_ Hstate].
  assert (Hi_eq : i = lst_size_pre) by lia.
  subst i.
  subst output_rows.
  exact PreH14.
Qed.

Lemma proof_of_sorted_list_sum_partial_solve_wit_5_pure_split_goal_3 : sorted_list_sum_partial_solve_wit_5_pure_split_goal_3.
Proof.
  unfold sorted_list_sum_partial_solve_wit_5_pure_split_goal_3.
  intros.
  entailer!.
Qed.

Lemma proof_of_sorted_list_sum_partial_solve_wit_5_pure : sorted_list_sum_partial_solve_wit_5_pure.
Proof.
  unfold sorted_list_sum_partial_solve_wit_5_pure.
  right.
  intros.
  pose proof PreH18 as Hwf.
  destruct Hwf as [_ [Hsize_lt _]].
  assert (Hrows_len :
    output_size = rows_length_149 (filter_even_prefix_149 rows lst_size_pre)).
  {
    unfold rows_length_149.
    destruct PreH20 as [_ Hstate].
    assert (Hi_eq : i = lst_size_pre) by lia.
    subst i.
    subst output_rows.
    exact PreH14.
  }
  assert (Hptrs_len : output_size = ptrs_length_149 output_ptrs).
  {
    unfold ptrs_length_149.
    exact PreH15.
  }
  entailer!.
  all: try exact Hsize_lt; try exact Hrows_len; try exact Hptrs_len.
Qed.
