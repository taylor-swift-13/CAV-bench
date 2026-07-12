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

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.



Lemma string_length_string_of_list_z_149 : forall l,
  String.length (string_of_list_z_149 l) = List.length l.
Proof.
  induction l as [|x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_149 : forall row,
  Z.of_nat (String.length (row_string_z_149 row)) = row_len_z_149 row.
Proof.
  intros row.
  unfold row_string_z_149, row_len_z_149, string_lib.string_length.
  rewrite string_length_string_of_list_z_149.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma Z_even_odd_of_nat_149 : forall n,
  Z.even (Z.of_nat n) = Nat.even n /\
  Z.odd (Z.of_nat n) = Nat.odd n.
Proof.
  induction n as [|n [IHeven IHodd]].
  - split; reflexivity.
  - rewrite Nat2Z.inj_succ.
    split.
    + rewrite Z.even_succ, Nat.even_succ.
      exact IHodd.
    + rewrite Z.odd_succ, Nat.odd_succ.
      exact IHeven.
Qed.

Lemma Z_even_of_nat_149 : forall n,
  Z.even (Z.of_nat n) = Nat.even n.
Proof.
  intro n.
  apply Z_even_odd_of_nat_149.
Qed.

Lemma even_row_has_even_length_149 : forall row,
  even_row_z_149 row = has_even_length (row_string_z_149 row).
Proof.
  intros row.
  unfold even_row_z_149, has_even_length.
  rewrite <- row_string_length_z_149.
  apply Z_even_of_nat_149.
Qed.

Lemma rows_well_formed_149_row : forall rows n k,
  rows_well_formed_149 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_149 row in
    row = string_lib.c_string payload /\
    string_lib.valid_string payload /\
    string_lib.string_length payload < INT_MAX.
Proof.
  intros rows n k [_ [_ Hrows]] Hk.
  specialize (Hrows k Hk).
  tauto.
Qed.

Lemma c_string_Zlength_149 : forall payload,
  Zlength (string_lib.c_string payload) = string_lib.string_length payload + 1.
Proof.
  intros payload.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_149 : forall rows n k,
  rows_well_formed_149 rows n ->
  0 <= k < n ->
  string_lib.c_string (row_payload_z_149 (Znth k rows nil)) =
  Znth k rows nil.
Proof.
  intros rows n k Hwf Hk.
  pose proof (rows_well_formed_149_row rows n k Hwf Hk) as Hrow.
  simpl in Hrow.
  destruct Hrow as [Hrow _].
  symmetry.
  exact Hrow.
Qed.

Lemma row_payload_c_string_payload_149 : forall payload,
  row_payload_z_149 (string_lib.c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_149, string_lib.c_string.
  replace (Z.to_nat (Zlength (payload ++ [0]) - 1)) with (List.length payload).
  - change (firstn (List.length payload) (payload ++ [0]) = payload).
    rewrite firstn_app.
    rewrite firstn_all.
    rewrite Nat.sub_diag.
    simpl.
    rewrite app_nil_r.
    reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Zlength_correct.
    replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
      with (Z.of_nat (List.length payload)) by lia.
    symmetry.
    apply Nat2Z.id.
Qed.

Lemma filter_even_rows_149_app_take : forall rows row,
  even_row_z_149 row = true ->
  filter_even_rows_149 (rows ++ [row]) =
  filter_even_rows_149 rows ++ [row].
Proof.
  induction rows as [|h t IH]; intros row Heven; simpl.
  - rewrite Heven. reflexivity.
  - destruct (even_row_z_149 h); simpl; rewrite IH by exact Heven; reflexivity.
Qed.

Lemma filter_even_rows_149_app_keep : forall rows row,
  even_row_z_149 row = false ->
  filter_even_rows_149 (rows ++ [row]) =
  filter_even_rows_149 rows.
Proof.
  induction rows as [|h t IH]; intros row Heven; simpl.
  - rewrite Heven. reflexivity.
  - destruct (even_row_z_149 h); simpl; rewrite IH by exact Heven; reflexivity.
Qed.

Lemma filter_even_prefix_149_snoc : forall (rows : list (list Z)) i,
  0 <= i < Zlength rows ->
  firstn (Z.to_nat (i + 1)) rows =
  firstn (Z.to_nat i) rows ++ [Znth i rows (@nil Z)].
Proof.
  assert (Hnth: forall (rows : list (list Z)) n,
    (n < List.length rows)%nat ->
    firstn (S n) rows = firstn n rows ++ [nth n rows nil]).
  {
    induction rows as [| row rest IH]; intros [| n] Hlt; simpl in *; try lia.
    - reflexivity.
    - rewrite IH by lia.
      reflexivity.
  }
  intros rows i Hi.
  assert (Hsucc: Z.to_nat (i + 1) = S (Z.to_nat i)).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    lia.
  }
  rewrite Hsucc.
  rewrite Hnth.
  - unfold Znth.
    reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.

Lemma filter_even_step_take_149_valid : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = true ->
  filter_even_state_149 rows (i + 1)
    (output_rows ++ [Znth i rows nil]).
Proof.
  intros rows i output_rows Hi [Hrange Hstate] Heven.
  split; [lia|].
  unfold filter_even_prefix_149 in *.
  rewrite filter_even_prefix_149_snoc by lia.
  rewrite filter_even_rows_149_app_take by exact Heven.
  subst output_rows.
  reflexivity.
Qed.

Lemma filter_even_step_keep_149_valid : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = false ->
  filter_even_state_149 rows (i + 1) output_rows.
Proof.
  intros rows i output_rows Hi [Hrange Hstate] Heven.
  split; [lia|].
  unfold filter_even_prefix_149 in *.
  rewrite filter_even_prefix_149_snoc by lia.
  rewrite filter_even_rows_149_app_keep by exact Heven.
  exact Hstate.
Qed.

Lemma filter_even_step_take_149_intro : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = true ->
  filter_even_step_take_149 rows i output_rows
    (output_rows ++ [Znth i rows nil]).
Proof.
  unfold filter_even_step_take_149.
  intros rows i output_rows Hi Hstate Heven.
  split; [reflexivity|].
  eapply filter_even_step_take_149_valid; eauto.
Qed.

Lemma filter_even_step_keep_149_intro : forall rows i output_rows,
  0 <= i < Zlength rows ->
  filter_even_state_149 rows i output_rows ->
  even_row_z_149 (Znth i rows nil) = false ->
  filter_even_step_keep_149 rows i output_rows.
Proof.
  unfold filter_even_step_keep_149.
  intros rows i output_rows Hi Hstate Heven.
  eapply filter_even_step_keep_149_valid; eauto.
Qed.

Lemma Z_even_true_of_rem2_149 : forall z,
  0 <= z ->
  Z.rem z 2 = 0 ->
  Z.even z = true.
Proof.
  intros z Hz Hrem.
  apply Z.even_spec.
  rewrite Z.rem_mod_nonneg in Hrem by lia.
  apply (proj1 (Z.mod_divide z 2 ltac:(lia))) in Hrem.
  destruct Hrem as [k Hk].
  exists k.
  lia.
Qed.

Lemma Z_even_false_of_rem2_nonzero_149 : forall z,
  0 <= z ->
  Z.rem z 2 <> 0 ->
  Z.even z = false.
Proof.
  intros z Hz Hrem.
  destruct (Z.even z) eqn:Heven; [| reflexivity].
  exfalso.
  apply Hrem.
  rewrite Z.rem_mod_nonneg by lia.
  apply (proj2 (Z.mod_divide z 2 ltac:(lia))).
  apply Z.even_spec in Heven.
  destruct Heven as [k Hk].
  exists k.
  lia.
Qed.

Lemma filter_even_rows_to_strings_149 : forall rows,
  rows_to_strings_z_149 (filter_even_rows_149 rows) =
  filter has_even_length (rows_to_strings_z_149 rows).
Proof.
  induction rows as [|row rest IH]; simpl; [reflexivity|].
  rewrite <- even_row_has_even_length_149.
  destruct (even_row_z_149 row); simpl; rewrite IH; reflexivity.
Qed.

Lemma filter_even_state_full_149 : forall rows filtered,
  filter_even_state_149 rows (Zlength rows) filtered ->
  rows_to_strings_z_149 filtered =
  filter has_even_length (rows_to_strings_z_149 rows).
Proof.
  intros rows filtered [_ Hfiltered].
  subst filtered.
  unfold filter_even_prefix_149.
  rewrite firstn_all2.
  - apply filter_even_rows_to_strings_149.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma problem_149_spec_z_of_sorted_filter_valid : forall rows filtered sorted,
  filter_even_state_149 rows (Zlength rows) filtered ->
  Permutation_rows_149 filtered sorted ->
  string_rows_sorted_149 sorted ->
  problem_149_spec_z rows sorted.
Proof.
  intros rows filtered sorted Hfilter Hperm Hsorted.
  unfold problem_149_spec_z, problem_149_spec, string_rows_sorted_149 in *.
  split.
  - rewrite <- filter_even_state_full_149 with (filtered := filtered) by exact Hfilter.
    unfold rows_to_strings_z_149.
    apply Permutation_sym.
    apply Permutation_map.
    exact Hperm.
  - exact Hsorted.
Qed.

Lemma problem_149_spec_z_of_sorted_filter_intro : forall rows filtered sorted,
  problem_149_spec_z_of_sorted_filter rows filtered sorted.
Proof.
  unfold problem_149_spec_z_of_sorted_filter.
  intros rows filtered sorted Hfilter Hperm Hsorted.
  eapply problem_149_spec_z_of_sorted_filter_valid; eauto.
Qed.

Lemma problem_149_spec_z_of_sorted_prefix_intro : forall rows sorted,
  problem_149_spec_z_of_sorted_prefix rows sorted.
Proof.
  unfold problem_149_spec_z_of_sorted_prefix.
  intros rows sorted Hperm Hsorted.
  apply problem_149_spec_z_of_sorted_filter_valid
    with (filtered := filter_even_prefix_149 rows (Zlength rows)); auto.
  split.
  - pose proof (Zlength_nonneg rows).
    lia.
  - reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

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
