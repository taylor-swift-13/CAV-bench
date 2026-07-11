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
From SimpleC.EE.CAV.ground_truth_p113_odd_count Require Import p113_odd_count_goal.
From SimpleC.EE.CAV.ground_truth_p113_odd_count Require Import p113_odd_count_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p113_odd_count.
Local Open Scope sac.

Lemma proof_of_odd_count_safety_wit_25 : odd_count_safety_wit_25.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_26 : odd_count_safety_wit_26.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_27 : odd_count_safety_wit_27.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia.
Qed.

Lemma proof_of_odd_count_safety_wit_40 : odd_count_safety_wit_40.
Proof.
  left; intros; apply _derivable1_andp_intros; apply dump_spatial_left;
    pose proof template_len_113_value; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_1 : odd_count_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    intros.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_2 lst_size_pre).
    rewrite PtrArray.seg_empty.
    sep_apply_l_atomic (GlobalStrings_split LitMap template_literal_113).
    unfold template_literal_113.
    entailer!.
    + simpl. rewrite Z.add_0_r. entailer!.
    + apply odd_count_state_113_initial.
    + pose proof template_len_113_value; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_2 : odd_count_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH20 ltac:(lia))
      as Hrow.
    simpl in Hrow.
    destruct Hrow as [Hrow_eq [Hvalid [Hascii [Hstrlen Hlen]]]].
    sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i lst_pre i lst_size_pre rows).
    + dump_pre_spatial. lia.
    + Intros row_ptr.
      Exists output_ptrs_2 row_ptr output_rows_2.
      unfold StorePtrAsElement.storeA.
      rewrite sizeof_ptr.
      change (CharPtrArray2.ElemArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil))
        with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
      unfold store_string.
      rewrite Hrow_eq.
      repeat rewrite row_payload_c_string_113.
      repeat rewrite c_string_Zlength_113.
      entailer!.
      apply valid_string_std_113; assumption.
Qed.

Lemma proof_of_odd_count_entail_wit_3 : odd_count_entail_wit_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    + rewrite PreH1.
      apply string_length_nonneg.
Qed.

Lemma proof_of_odd_count_entail_wit_4_1 : odd_count_entail_wit_4_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    rewrite PreH10.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    try rewrite (odd_digit_count_prefix_step_113
                   (row_payload_z_113 (row_at_113 i rows)) j Hj).
    change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
      with (c_string (row_payload_z_113 (row_at_113 i rows))).
    assert (Hrange :
      48 <= Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 <= 57)
      by lia.
    assert (Hmod :
      Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 mod 2 = 1)
      by (rewrite <- Z.rem_mod_nonneg by lia; exact PreH1).
    pose proof (is_odd_digit_z_113_true_mod _ Hrange Hmod) as Hodd.
    try rewrite Hodd.
    entailer!.
Qed.

Lemma proof_of_odd_count_entail_wit_4_2 : odd_count_entail_wit_4_2.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    entailer!.
    + apply (proj2 (row_payload_ascii_std_113 rows lst_size_pre i j PreH24 ltac:(lia) Hj)).
    + rewrite PreH9.
      rewrite (odd_digit_count_prefix_step_113
                 (row_payload_z_113 (row_at_113 i rows)) j Hj).
      change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
        with (c_string (row_payload_z_113 (row_at_113 i rows))).
      assert (Hgt :
        57 < Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0)
        by lia.
      pose proof (is_odd_digit_z_113_false_gt _ Hgt) as Hnotodd.
      rewrite Hnotodd.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_4_3 : odd_count_entail_wit_4_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    entailer!.
    + apply (proj1 (row_payload_ascii_std_113 rows lst_size_pre i j PreH23 ltac:(lia) Hj)).
    + rewrite PreH8.
      rewrite (odd_digit_count_prefix_step_113
                 (row_payload_z_113 (row_at_113 i rows)) j Hj).
      change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
        with (c_string (row_payload_z_113 (row_at_113 i rows))).
      pose proof (is_odd_digit_z_113_false_lt _ PreH1) as Hnotodd.
      rewrite Hnotodd.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_4_4 : odd_count_entail_wit_4_4.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    try rewrite PreH10.
    assert (Hj : 0 <= j <
      string_length (row_payload_z_113 (row_at_113 i rows))) by lia.
    rewrite (odd_digit_count_prefix_step_113
               (row_payload_z_113 (row_at_113 i rows)) j Hj).
    change (naive_C_Rules.c_string (row_payload_z_113 (row_at_113 i rows)))
      with (c_string (row_payload_z_113 (row_at_113 i rows))).
    assert (Hrange :
      48 <= Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 <= 57)
      by lia.
    assert (Hmod :
      Znth j (c_string (row_payload_z_113 (row_at_113 i rows))) 0 mod 2 <> 1)
      by (rewrite <- Z.rem_mod_nonneg by lia; exact PreH1).
    pose proof (is_odd_digit_z_113_false_even_digit _ Hrange Hmod) as Hnotodd.
    try rewrite Hnotodd.
    entailer!.
Qed.

Lemma proof_of_odd_count_entail_wit_5 : odd_count_entail_wit_5.
Proof.
  constructor.
  - pre_process_default.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH22 ltac:(lia))
      as Hrow.
    simpl in Hrow.
    destruct Hrow as [_ [_ [_ [Hstrlen _]]]].
    assert (Hsumrow : sum = odd_digit_count_row_113 (row_at_113 i rows)).
    {
      rewrite PreH7.
      unfold odd_digit_count_row_113.
      apply odd_digit_count_prefix_full_113.
      replace j with n by lia.
      exact PreH6.
    }
    Exists output_ptrs_2 output_rows_2.
    entailer!.
    + rewrite Hsumrow.
      apply PreH23.
      lia.
    + unfold row_at_113 in *.
      unfold nil_z_113 in *.
      unfold string_length, naive_C_Rules.string_length in *.
      lia.
Qed.

Lemma proof_of_odd_count_entail_wit_6 : odd_count_entail_wit_6.
Proof.
  constructor.
  - pre_process_default.
    assert (Houtlen_eq :
      56 + 4 * (retval - 1) =
      Zlength (odd_count_row_113 (row_at_113 i rows)) - 1).
    {
      rewrite odd_count_row_Zlength_113.
      rewrite <- PreH9.
      rewrite <- PreH4.
      lia.
    }
    assert (Houtlen_lt : 56 + 4 * (retval - 1) < INT_MAX).
    {
      pose proof (PreH27 i ltac:(lia)).
      lia.
    }
    Exists output_ptrs_2 output_rows_2 (@nil Z).
    sep_apply CharArray.undef_full_to_undef_seg.
    rewrite (CharArray.full_empty retval_2 0).
    entailer!.
    unfold template_fill_state_113.
    split.
    + rewrite template_len_113_value; lia.
    + split.
      * unfold template_prefix_payload_113; simpl; reflexivity.
      * rewrite Zlength_nil; lia.
Qed.

Lemma proof_of_odd_count_entail_wit_7 : odd_count_entail_wit_7.
Proof.
  constructor.
  - pre_process_default.
    assert (Hroom_bound : k + numlen <= outlen).
    {
      assert (Ht_range : 0 <= t < template_len_113).
      { rewrite template_len_113_value. lia. }
      pose proof (template_literal_i_room_113
                    t (decimal_digits_113 sum) k out_l_2
                    PreH13 Ht_range PreH1) as Hroom.
      assert (Houtlen_formula :
        outlen = 56 + 4 * (Zlength (decimal_digits_113 sum) - 1)).
      {
        rewrite PreH12.
        rewrite odd_count_row_Zlength_113.
        rewrite <- PreH8.
        lia.
      }
      rewrite template_replace_Zlength_113 in Hroom.
      rewrite PreH9.
      lia.
    }
    Exists output_ptrs_2 output_rows_2 out_l_2.
    sep_apply (CharArray.undef_seg_split_to_undef_seg row_out k (k + numlen) (outlen + 1)).
    2: { pose proof (Zlength_nonneg (decimal_digits_113 sum)); lia. }
    sep_apply (CharArray.undef_seg_to_undef_full row_out k (k + numlen)).
    replace (k + numlen - k) with numlen by lia.
    entailer!.
    apply decimal_digits_113_all_ascii.
    rewrite PreH8.
    apply odd_digit_count_row_113_nonneg.
Qed.

Lemma proof_of_odd_count_entail_wit_8_1 : odd_count_entail_wit_8_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2 (out_l_2 ++ decimal_digits_113 sum).
    pose proof (Zlength_nonneg (decimal_digits_113 sum)) as Hnumlen_nonneg.
    replace numlen with (k + numlen - k) at 1 by lia.
    sep_apply_l_atomic (CharArray.full_merge_to_full
                          row_out k (k + numlen) out_l_2 (decimal_digits_113 sum)).
    + dump_pre_spatial. lia.
    + entailer!.
      rewrite PreH10.
      apply template_literal_i_step_113; try exact PreH15; try lia.
Qed.

Lemma proof_of_odd_count_entail_wit_8_2 : odd_count_entail_wit_8_2.
Proof.
  constructor.
  - pre_process_default.
    assert (Hroom_bound : k + 1 <= outlen).
    {
      assert (Ht_range : 0 <= t < template_len_113).
      { rewrite template_len_113_value. lia. }
      pose proof (template_literal_non_i_room_113
                    t (decimal_digits_113 sum) k out_l_2
                    PreH16 Ht_range PreH4) as Hroom.
      rewrite template_replace_Zlength_113 in Hroom.
      assert (Houtlen_formula :
        outlen = 56 + 4 * (Zlength (decimal_digits_113 sum) - 1)).
      {
        rewrite PreH15.
        rewrite odd_count_row_Zlength_113.
        rewrite <- PreH11.
        lia.
      }
      lia.
    }
    Exists output_ptrs_2 output_rows_2
      (out_l_2 ++
       cons (signed_last_nbits
         (Znth t (StringToList template_literal_113 (StringLength template_literal_113 + 1)) 0) 8) nil).
    entailer!.
    + pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia)).
      lia.
    + pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia)).
      lia.
    + apply template_literal_non_i_step_113; try exact PreH16; try lia.
      rewrite template_len_113_value; lia.
    + rewrite template_len_113_value; lia.
    all: try solve [
      pose proof (template_literal_char_ascii_113 t ltac:(rewrite template_len_113_value; lia));
      lia
    ].
    all: try solve [
      apply template_literal_non_i_step_113; try exact PreH16; try lia;
      rewrite template_len_113_value; lia
    ].
    all: try solve [rewrite template_len_113_value; lia].
Qed.

Lemma proof_of_odd_count_entail_wit_9 : odd_count_entail_wit_9.
Proof.
  constructor.
  - pre_process_default.
    pose proof (odd_count_row_complete_113
                  (row_at_113 i rows) sum t k out_l
                  PreH11 PreH16 PreH5 PreH7) as [Hrow Hrowlen].
    assert (Ht_eq : t = template_len_113).
    { pose proof template_len_113_value. lia. }
    assert (Hk_outlen : k = outlen).
    {
      rewrite PreH15.
      rewrite <- Hrowlen.
      lia.
    }
    prop_apply (PtrArray.seg_Zlength data 0 (i + 1) (output_ptrs_2 ++ row_out :: nil)).
    Intros_p Hseg_output_len.
    assert (Houtput_ptrs_len : Zlength output_ptrs_2 = i).
    {
      rewrite Zlength_app, Zlength_cons, Zlength_nil in Hseg_output_len.
      lia.
    }
    Exists (output_ptrs_2 ++ row_out :: nil)
           (output_rows_2 ++ odd_count_row_113 (row_at_113 i rows) :: nil).
    rewrite sizeof_ptr.
    pose proof (rows_well_formed_113_row rows lst_size_pre i PreH24 ltac:(lia))
      as Hinput_row.
    simpl in Hinput_row.
    destruct Hinput_row as [Hinput_eq [_ [_ [Hinput_lt Hinput_len]]]].
    assert (Hsum_lt : sum < INT_MAX).
    {
      rewrite PreH11.
      unfold odd_digit_count_row_113.
      pose proof (count_odd_digits_payload_113_le_Zlength
                    (row_payload_z_113 (row_at_113 i rows))) as Hcount_le.
      unfold row_at_113, nil_z_113 in Hcount_le |- *.
      change (naive_C_Rules.string_length (row_payload_z_113 (Znth i rows nil)))
        with (string_length (row_payload_z_113 (Znth i rows nil))) in Hinput_lt.
      unfold string_length in Hinput_lt.
      lia.
    }
    assert (Hsum_nonneg : 0 <= sum).
    {
      rewrite PreH11.
      apply odd_digit_count_row_113_nonneg.
    }
    assert (Hn_lt : n < INT_MAX).
    {
      rewrite PreH10.
      unfold row_at_113, nil_z_113 in Hinput_lt |- *.
      change (naive_C_Rules.string_length (row_payload_z_113 (Znth i rows nil)))
        with (string_length (row_payload_z_113 (Znth i rows nil))) in Hinput_lt.
      exact Hinput_lt.
    }
    assert (Hn_nonneg : 0 <= n).
    {
      rewrite PreH10.
      unfold string_length.
      apply Zlength_nonneg.
    }
    assert (Hnumlen_room : 0 <= numlen + 1 <= 32).
    {
      specialize (PreH25 i ltac:(lia)) as Hdigits_room.
      rewrite <- PreH11 in Hdigits_room.
      rewrite <- PreH12 in Hdigits_room.
      lia.
    }
    pose proof (CharPtrArray2.missing_i_merge_to_full
      lst_pre i lst_size_pre row_ptr rows
      (c_string (row_payload_z_113 (row_at_113 i rows)))) as Hmerge.
    unfold StorePtrAsElement.storeA in Hmerge.
    rewrite c_string_Zlength_113 in Hmerge.
    change (naive_C_Rules.string_length (row_payload_z_113 (row_at_113 i rows)))
      with (string_length (row_payload_z_113 (row_at_113 i rows))) in Hmerge.
    change (CharPtrArray2.ElemArray.full row_ptr
      (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
      (c_string (row_payload_z_113 (row_at_113 i rows))))
      with (CharArray.full row_ptr
        (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
        (c_string (row_payload_z_113 (row_at_113 i rows)))) in Hmerge.
    sep_lift_L
      ((((lst_pre + i * 4) # Ptr |-> row_ptr)) ::
       (CharArray.full row_ptr
          (string_length (row_payload_z_113 (row_at_113 i rows)) + 1)
          (c_string (row_payload_z_113 (row_at_113 i rows)))) ::
       (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows) :: nil).
    sep_apply Hmerge; try lia.
    assert (Hreplace_rows :
      replace_Znth i (c_string (row_payload_z_113 (row_at_113 i rows))) rows = rows).
    {
      unfold row_at_113, nil_z_113.
      change (c_string (row_payload_z_113 (Znth i rows nil)))
        with (naive_C_Rules.c_string (row_payload_z_113 (Znth i rows nil))).
      rewrite <- Hinput_eq.
      apply replace_Znth_Znth.
    }
    rewrite Hreplace_rows.
    unfold store_string.
    replace (out_l ++ 0 :: nil) with (odd_count_row_113 (row_at_113 i rows))
      by (symmetry; exact Hrow).
    replace (k + 1) with (Zlength (odd_count_row_113 (row_at_113 i rows)))
      by (symmetry; exact Hrowlen).
    replace (outlen + 1) with (Zlength (odd_count_row_113 (row_at_113 i rows))) by lia.
    rewrite (CharArray.undef_seg_empty row_out
      (Zlength (odd_count_row_113 (row_at_113 i rows)))).
    sep_apply (odd_count_rows_heap_113_snoc
                 output_ptrs_2 output_rows_2 row_out
                 (odd_count_row_113 (row_at_113 i rows))).
    sep_apply (CharArray.full_to_undef_full numbuf numlen (decimal_digits_113 sum)).
    sep_apply (CharArray.full_to_undef_full (numbuf + numlen * sizeof(CHAR)) 1 (0 :: nil)).
    replace 1 with (numlen + 1 - numlen) at 1 by lia.
    sep_lift_L
      ((CharArray.undef_full numbuf numlen) ::
       (CharArray.undef_full (numbuf + numlen * sizeof(CHAR)) (numlen + 1 - numlen)) :: nil).
    sep_apply (CharArray.undef_full_merge_to_undef_full numbuf numlen (numlen + 1)).
    sep_apply (CharArray.undef_full_to_undef_seg numbuf (numlen + 1)).
    replace (numbuf + 0 * sizeof(CHAR)) with numbuf by lia.
    replace (numlen + 1 - 0) with (numlen + 1) by lia.
    sep_apply (CharArray.undef_seg_merge_to_undef_full numbuf 0 (numlen + 1) 32).
    replace (numbuf + 0 * sizeof(CHAR)) with numbuf by lia.
    replace (32 - 0) with 32 by lia.
    cancel.
    entailer!.
    -- assert (Hrows_len_total : Zlength rows = lst_size_pre).
       { destruct PreH24 as [Hlen _]; exact Hlen. }
       apply odd_count_state_113_snoc; try exact PreH28.
       rewrite Hrows_len_total; lia.
    -- exact Hnumlen_room.
    -- split; [exact PreH4 | lia].
    -- rewrite Houtput_ptrs_len.
       symmetry.
       apply odd_count_state_113_Zlength with (rows := rows).
       exact PreH28.
Qed.

Lemma proof_of_odd_count_return_wit_1 : odd_count_return_wit_1.
Proof.
  constructor.
  pre_process_default.
  assert (Hi_eq : i = lst_size_pre) by lia.
  subst i.
  assert (Houtput_rows_eq : output_rows_2 = odd_count_rows_113 rows).
  {
    destruct PreH24 as [_ Hrows_state].
    unfold odd_count_rows_113 in Hrows_state |- *.
    rewrite firstn_all2 in Hrows_state.
    - exact Hrows_state.
    - destruct PreH20 as [Hlen _].
      rewrite Zlength_correct in Hlen.
      lia.
  }
  Exists numbuf output_ptrs_2 (odd_count_rows_113 rows) data_2.
  rewrite Hi_eq.
  rewrite (PtrArray.undef_seg_empty data_2 lst_size_pre).
  rewrite Houtput_rows_eq.
  rewrite PreH26.
  sep_apply (GlobalStrings_merge LitMap template_literal_113).
  entailer!.
  - apply odd_count_rows_spec_113 with (n := lst_size_pre).
    exact PreH20.
  - rewrite <- Houtput_rows_eq.
    rewrite <- Hi_eq.
    apply odd_count_state_113_Zlength with (rows := rows).
    exact PreH24.
Qed.
