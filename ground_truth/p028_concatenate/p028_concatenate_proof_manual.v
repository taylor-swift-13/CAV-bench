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

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.



Lemma String_length_string_of_list_z_28 : forall l,
  String.length (string_of_list_z_28 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_28 : forall row,
  Z.of_nat (String.length (row_string_z_28 row)) = row_len_z_28 row.
Proof.
  intros row.
  unfold row_string_z_28, row_len_z_28, string_length.
  rewrite String_length_string_of_list_z_28.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma rows_well_formed_28_row : forall rows n k,
  rows_well_formed_28 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_28 row in
  row = c_string payload /\
  valid_string payload /\
  all_ascii payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid [Hascii Hlt]]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hascii|].
  split; [exact Hlt|].
  subst row payload.
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_28 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma c_string_payload_prefix_28 : forall payload,
  sublist 0 (string_length payload) (c_string payload) = payload.
Proof.
  intros payload.
  unfold c_string, string_length.
  apply sublist_app_exact1.
Qed.

Lemma row_payload_c_string_28 : forall payload,
  row_payload_z_28 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_28, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1.
  replace (Zlength payload + 1 - 1) with (Zlength payload) by lia.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app, firstn_all.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma c_string_payload_nul_28 : forall payload,
  sublist (string_length payload) (string_length payload + 1)
    (c_string payload) = cons 0 nil.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite (sublist_split_app_r (Zlength payload) (Zlength payload + 1)
    (Zlength payload) payload (cons 0 nil)).
  - replace (Zlength payload - Zlength payload) with 0 by lia.
    replace (Zlength payload + 1 - Zlength payload) with 1 by lia.
    apply sublist_self.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  - reflexivity.
  - lia.
Qed.

Lemma total_prefix_state_28_initial : forall rows,
  total_prefix_state_28 rows 0 1.
Proof.
  intros rows.
  unfold total_prefix_state_28, concat_prefix_len_28,
    concat_prefix_payload_28.
  split; [rewrite Zlength_correct; lia|].
  simpl.
  lia.
Qed.

Lemma firstn_succ_Z_28 : forall (rows : list (list Z)) k,
  0 <= k < Zlength rows ->
  firstn (Z.to_nat (k + 1)) rows =
  firstn (Z.to_nat k) rows ++ [Znth k rows nil].
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
  intros rows k Hk.
  assert (Hsucc: Z.to_nat (k + 1) = S (Z.to_nat k)).
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

Lemma concat_rows_payload_28_app : forall a b,
  concat_rows_payload_28 (a ++ b) =
  concat_rows_payload_28 a ++ concat_rows_payload_28 b.
Proof.
  induction a as [| row rest IH]; simpl; intros b.
  - reflexivity.
  - rewrite IH, app_assoc.
    reflexivity.
Qed.

Lemma concat_prefix_payload_28_step : forall rows k,
  0 <= k < Zlength rows ->
  concat_prefix_payload_28 rows (k + 1) =
  concat_prefix_payload_28 rows k ++ row_payload_z_28 (Znth k rows nil).
Proof.
  intros rows k Hk.
  unfold concat_prefix_payload_28.
  rewrite firstn_succ_Z_28 by exact Hk.
  rewrite concat_rows_payload_28_app.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma concat_rows_payload_28_firstn_mono_nat : forall rows a b,
  (a <= b)%nat ->
  Zlength (concat_rows_payload_28 (firstn a rows)) <=
  Zlength (concat_rows_payload_28 (firstn b rows)).
Proof.
  induction rows as [| row rest IH]; intros [| a] [| b] Hab; simpl in *; try lia.
  - apply Zlength_nonneg.
  - repeat rewrite Zlength_app.
    specialize (IH a b).
    lia.
Qed.

Lemma concat_prefix_len_monotone_28 : forall rows a b,
  0 <= a <= b ->
  concat_prefix_len_28 rows a <= concat_prefix_len_28 rows b.
Proof.
  intros rows a b Hab.
  unfold concat_prefix_len_28, concat_prefix_payload_28.
  apply concat_rows_payload_28_firstn_mono_nat.
  apply Z2Nat.inj_le; lia.
Qed.

Lemma copy_prefix_state_28_room : forall rows n i k out_l total,
  rows_well_formed_28 rows n ->
  total_prefix_state_28 rows n total ->
  copy_prefix_state_28 rows i k out_l ->
  0 <= i < n ->
  k + row_len_z_28 (Znth i rows nil) < total.
Proof.
  intros rows n i k out_l total Hwf Htotal Hcopy Hi.
  destruct Hwf as [Hrows _].
  unfold total_prefix_state_28 in Htotal.
  unfold copy_prefix_state_28 in Hcopy.
  destruct Htotal as [_ Htotal].
  destruct Hcopy as [_ [Hout Hk]].
  subst total k out_l.
  assert (Hmono:
    concat_prefix_len_28 rows (i + 1) <= concat_prefix_len_28 rows n).
  {
    apply concat_prefix_len_monotone_28.
    lia.
  }
  unfold concat_prefix_len_28 in Hmono.
  rewrite concat_prefix_payload_28_step in Hmono by lia.
  rewrite Zlength_app in Hmono.
  unfold concat_prefix_len_28.
  unfold row_len_z_28, string_length in *.
  lia.
Qed.

Lemma total_prefix_state_28_step : forall rows k total len,
  total_prefix_state_28 rows k total ->
  0 <= k < Zlength rows ->
  len = row_len_z_28 (Znth k rows nil) ->
  total_prefix_state_28 rows (k + 1) (total + len).
Proof.
  intros rows k total len [Hkbounds Htotal] Hk Hlen.
  unfold total_prefix_state_28, concat_prefix_len_28 in *.
  split; [lia|].
  rewrite concat_prefix_payload_28_step by exact Hk.
  rewrite Zlength_app.
  subst total len.
  unfold row_len_z_28, string_length.
  lia.
Qed.

Lemma copy_prefix_state_28_initial : forall rows,
  copy_prefix_state_28 rows 0 0 nil.
Proof.
  intros rows.
  unfold copy_prefix_state_28, concat_prefix_payload_28.
  split; [rewrite Zlength_correct; lia|].
  simpl.
  repeat split; rewrite ?Zlength_nil; reflexivity.
Qed.

Lemma copy_prefix_state_28_step : forall rows k pos out_l bytes,
  copy_prefix_state_28 rows k pos out_l ->
  0 <= k < Zlength rows ->
  bytes = row_payload_z_28 (Znth k rows nil) ->
  copy_prefix_state_28 rows (k + 1) (pos + Zlength bytes) (out_l ++ bytes).
Proof.
  intros rows k pos out_l bytes [Hkbounds [Hout Hpos]] Hk Hbytes.
  unfold copy_prefix_state_28 in *.
  split; [lia|].
  split.
  - rewrite concat_prefix_payload_28_step by exact Hk.
    subst out_l bytes.
    reflexivity.
  - rewrite Zlength_app.
    subst pos bytes.
    lia.
Qed.

Lemma string_of_list_z_28_app : forall a b,
  string_of_list_z_28 (a ++ b) =
  String.append (string_of_list_z_28 a) (string_of_list_z_28 b).
Proof.
  induction a as [| x xs IH]; simpl; intros b; congruence.
Qed.

Lemma string_append_empty_r_28 : forall s,
  String.append s EmptyString = s.
Proof.
  induction s as [| a s IH]; simpl; congruence.
Qed.

Lemma string_of_concat_rows_payload_28 : forall rows,
  string_of_list_z_28 (concat_rows_payload_28 rows) =
  String.concat "" (rows_to_strings_z_28 rows).
Proof.
  induction rows as [| row rest IH]; simpl.
  - reflexivity.
  - unfold row_string_z_28.
    rewrite string_of_list_z_28_app.
    rewrite IH.
    destruct (rows_to_strings_z_28 rest) as [| s ss]; simpl.
    + apply string_append_empty_r_28.
    + reflexivity.
Qed.

Lemma problem_28_spec_z_intro : forall rows out_l,
  out_l = concat_prefix_payload_28 rows (Zlength rows) ->
  problem_28_spec_z rows out_l.
Proof.
  intros rows out_l Hout.
  unfold problem_28_spec_z, problem_28_spec.
  subst out_l.
  unfold concat_prefix_payload_28.
  rewrite firstn_all2.
  - symmetry.
    apply string_of_concat_rows_payload_28.
  - rewrite Zlength_correct.
    rewrite Nat2Z.id.
    lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

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
