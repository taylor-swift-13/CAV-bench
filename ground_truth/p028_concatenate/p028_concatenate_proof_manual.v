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
From SimpleC.EE.CAV.ground_truth_p028_concatenate Require Import p028_concatenate_goal.
From SimpleC.EE.CAV.ground_truth_p028_concatenate Require Import p028_concatenate_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p028_concatenate.
Local Open Scope sac.

Ltac c28_row_facts :=
  match goal with
  | Hwf : rows_well_formed_28 ?rs ?n |- context[row_payload_z_28 (Znth ?i ?rs nil)] =>
      let Hrow := fresh "Hrow" in
      let Hvalid := fresh "Hvalid" in
      let Hascii := fresh "Hascii" in
      let Hlt := fresh "Hlt" in
      let Hlen := fresh "Hlen" in
      pose proof (rows_well_formed_28_row rs n i Hwf ltac:(lia))
        as [Hrow [Hvalid [Hascii [Hlt Hlen]]]]
  end.

Lemma proof_of_concatenate_entail_wit_1 : concatenate_entail_wit_1.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  apply total_prefix_state_28_initial.
Qed.

Lemma proof_of_concatenate_entail_wit_2 : concatenate_entail_wit_2.
Proof.
  pre_process_default.
  c28_row_facts.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    strings_pre i strings_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
    unfold store_string.
    rewrite <- Hlen, <- Hrow.
    entailer!.
Qed.

Lemma proof_of_concatenate_entail_wit_4 : concatenate_entail_wit_4.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  - c28_row_facts.
    unfold store_string.
    rewrite <- Hlen, <- Hrow.
    entailer!.
  - subst retval.
    apply string_length_nonneg.
  - subst retval.
    assert (Hi_rows : 0 <= i < Zlength rows).
    {
      destruct PreH13 as [Hrows_len _].
      rewrite Hrows_len.
      lia.
    }
    pose proof (total_prefix_state_28_step rows i total
      (row_len_z_28 (Znth i rows nil)) PreH16 Hi_rows eq_refl) as Hstep.
    unfold total_prefix_state_28, concat_prefix_len_28 in Hstep.
    destruct Hstep as [_ Htotal].
    unfold row_len_z_28 in *.
    specialize (PreH14 (i + 1) ltac:(lia)).
    unfold concat_prefix_len_28 in PreH14.
    lia.
Qed.

Lemma proof_of_concatenate_entail_wit_5 : concatenate_entail_wit_5.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  - pose proof (CharPtrArray2.missing_i_merge_to_full
      strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
    rewrite sizeof_ptr.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    entailer!.
  - unfold total_prefix_state_28, concat_prefix_len_28 in PreH16.
    destruct PreH16 as [_ Htotal].
    pose proof (Zlength_nonneg (concat_prefix_payload_28 rows i)).
    lia.
  - assert (Hi_rows : 0 <= i < Zlength rows).
    {
      destruct PreH13 as [Hrows_len _].
      rewrite Hrows_len.
      lia.
    }
    eapply total_prefix_state_28_step; eauto; lia.
Qed.

Lemma proof_of_concatenate_entail_wit_7 : concatenate_entail_wit_7.
Proof.
  pre_process_default.
  subst k.
  Exists (@nil Z).
  rewrite CharArray.full_empty.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval total).
  entailer!.
  - apply copy_prefix_state_28_initial.
  - assert (i = strings_size_pre) by lia.
    subst i.
    exact PreH16.
Qed.

Lemma proof_of_concatenate_entail_wit_8 : concatenate_entail_wit_8.
Proof.
  pre_process_default.
  c28_row_facts.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    strings_pre i strings_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    match goal with
    | Hcopy : copy_prefix_state_28 _ _ _ ?out_l |- _ =>
        Exists row_ptr out_l
    end.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
    unfold store_string.
    rewrite <- Hlen, <- Hrow.
    entailer!.
Qed.

Lemma proof_of_concatenate_entail_wit_10 : concatenate_entail_wit_10.
Proof.
  pre_process_default.
  c28_row_facts.
  match goal with
  | Hcopy : copy_prefix_state_28 _ _ _ ?out_l |- _ =>
      Exists out_l
  end.
  unfold store_string.
  rewrite <- Hlen, <- Hrow.
  entailer!.
  - subst retval.
    rewrite Hlen.
    sep_apply_l_atomic (CharArray.full_split_to_seg row_ptr
      (string_length (row_payload_z_28 (Znth i rows nil)))
      (string_length (row_payload_z_28 (Znth i rows nil)) + 1)
      (Znth i rows nil)).
    + entailer!.
      apply string_length_nonneg.
    + rewrite Hrow.
      repeat rewrite row_payload_c_string_28.
      rewrite c_string_payload_prefix_28.
      rewrite c_string_payload_nul_28.
      sep_apply_l_atomic (CharArray.seg_to_full row_ptr 0
        (string_length (row_payload_z_28 (Znth i rows nil)))
        (row_payload_z_28 (Znth i rows nil))).
      sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_seg out k
        (k + string_length (row_payload_z_28 (Znth i rows nil))) total);
        [ entailer!;
        pose proof (string_length_nonneg
          (row_payload_z_28 (Znth i rows nil)));
        assert (Hi_room : 0 <= i < strings_size_pre) by lia;
        pose proof (copy_prefix_state_28_room rows strings_size_pre i k out_l_2
          total PreH12 PreH15 PreH16 Hi_room);
        unfold row_len_z_28 in *;
        lia | ].
      sep_apply_l_atomic (CharArray.undef_seg_to_undef_full out k
        (k + string_length (row_payload_z_28 (Znth i rows nil)))).
      replace (row_ptr + 0 * sizeof(CHAR)) with row_ptr by lia.
      replace (string_length (row_payload_z_28 (Znth i rows nil)) - 0)
        with (string_length (row_payload_z_28 (Znth i rows nil))) by lia.
      replace (k + string_length (row_payload_z_28 (Znth i rows nil)) - k)
        with (string_length (row_payload_z_28 (Znth i rows nil))) by lia.
      cancel.
  - subst retval. apply string_length_nonneg.
  - subst retval.
    assert (Hi_room : 0 <= i < strings_size_pre) by lia.
    pose proof (copy_prefix_state_28_room rows strings_size_pre i k out_l_2
      total PreH12 PreH15 PreH16 Hi_room).
    unfold row_len_z_28 in *.
    lia.
Qed.

Lemma proof_of_concatenate_entail_wit_11 : concatenate_entail_wit_11.
Proof.
  pre_process_default.
  c28_row_facts.
  Exists (out_l_2 ++ row_payload_z_28 (Znth i rows nil)).
  sep_apply_l_atomic (CharArray.seg_to_full row_ptr len (len + 1) (0 :: nil)).
  sep_apply_l_atomic (CharArray.full_merge_to_full row_ptr len (len + 1)
    (row_payload_z_28 (Znth i rows nil)) (0 :: nil));
    [ entailer!;
      rewrite PreH19;
      pose proof (Zlength_nonneg (row_payload_z_28 (Znth i rows nil)));
      lia | ].
  change (app (row_payload_z_28 (Znth i rows nil)) (0 :: nil))
      with (c_string (row_payload_z_28 (Znth i rows nil))).
    replace (len + 1) with (Zlength (Znth i rows nil)) by
      (unfold row_len_z_28, string_length in *; lia).
    rewrite <- Hrow.
    rewrite sizeof_ptr.
    pose proof (CharPtrArray2.missing_i_merge_to_full
      strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil))
        (Znth i rows nil)) in Hmerge.
    sep_apply Hmerge; try lia.
    rewrite replace_Znth_Znth by lia.
    pose proof (CharArray.full_merge_to_full out k (k + len)
      out_l_2 (row_payload_z_28 (Znth i rows nil))) as Houtmerge.
    replace (k + len - k) with len in Houtmerge by lia.
    sep_apply Houtmerge; try lia.
    entailer!.
    - replace (k + len) with
        (k + Zlength (row_payload_z_28 (Znth i rows nil))) by lia.
      eapply copy_prefix_state_28_step with
        (bytes := row_payload_z_28 (Znth i rows nil)).
      + exact PreH17.
      + destruct PreH13 as [Hrows _]. lia.
      + reflexivity.
Qed.

Lemma proof_of_concatenate_entail_wit_13 : concatenate_entail_wit_13.
Proof.
  pre_process_default.
  assert (Hi_done : i = strings_size_pre) by lia.
  subst i.
  Exists out_l_2.
  assert (Htotal_k : total = k + 1).
  {
    unfold total_prefix_state_28, copy_prefix_state_28 in *.
    destruct PreH13 as [_ Htotal].
    destruct PreH14 as [_ [Hout Hk]].
    subst total k out_l_2.
    unfold concat_prefix_len_28.
    lia.
  }
  rewrite Htotal_k.
  entailer!.
Qed.

Lemma proof_of_concatenate_entail_wit_14 : concatenate_entail_wit_14.
Proof.
  pre_process_default.
  Exists out_l_2.
  entailer!.
  - rewrite CharArray.undef_seg_empty.
    elim_emp.
    apply derivable1_refl.
  - eapply problem_28_spec_z_intro.
    unfold copy_prefix_state_28 in PreH10.
    destruct PreH10 as [_ [Hout _]].
    destruct PreH3 as [Hrows _].
    rewrite Hrows.
    exact Hout.
Qed.

Lemma proof_of_concatenate_return_wit_1 : concatenate_return_wit_1.
Proof.
  pre_process_default.
  Exists out_l_2.
  assert (Hout_len : k = Zlength out_l_2).
  {
    unfold copy_prefix_state_28 in PreH9.
    tauto.
  }
  rewrite <- Hout_len.
  entailer!.
Qed.
