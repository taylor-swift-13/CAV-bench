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

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.



Lemma String_length_string_of_list_z_29 : forall l,
  String.length (string_of_list_z_29 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_29 : forall row,
  Z.of_nat (String.length (row_string_z_29 row)) = row_len_z_29 row.
Proof.
  intros row.
  unfold row_string_z_29, row_len_z_29, string_length.
  rewrite String_length_string_of_list_z_29.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma rows_well_formed_29_row : forall rows n k,
  rows_well_formed_29 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_29 row in
  row = c_string payload /\
  valid_string payload /\
  string_length payload < INT_MAX /\
  Zlength row = string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hvalid Hlt]].
  split; [exact Hrow|].
  split; [exact Hvalid|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma row_payload_c_string_29 : forall payload,
  row_payload_z_29 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_29, c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite Zlength_correct.
  replace (Z.of_nat (List.length payload) + Z.succ 0 - 1)
    with (Z.of_nat (List.length payload)) by lia.
  rewrite Nat2Z.id.
  replace (List.length payload) with (List.length payload + 0)%nat by lia.
  rewrite firstn_app_2.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma c_string_Zlength_29 : forall payload,
  Zlength (c_string payload) = string_length payload + 1.
Proof.
  intros payload.
  unfold c_string, string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma filter_prefix_state_29_initial : forall rows prefix,
  filter_prefix_state_29 rows prefix 0 nil.
Proof.
  intros rows prefix.
  unfold filter_prefix_state_29, filter_prefix_prefix_29.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma firstn_succ_Z_29 : forall (rows : list (list Z)) k,
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

Lemma filter_prefix_rows_29_app : forall a b prefix,
  filter_prefix_rows_29 (a ++ b) prefix =
  filter_prefix_rows_29 a prefix ++ filter_prefix_rows_29 b prefix.
Proof.
  induction a as [| row rest IH]; simpl; intros b prefix.
  - reflexivity.
  - destruct (String.prefix (string_of_list_z_29 prefix) (row_string_z_29 row));
      rewrite IH; reflexivity.
Qed.

Lemma filter_prefix_prefix_29_step_add : forall rows prefix k out,
  filter_prefix_state_29 rows prefix k out ->
  0 <= k < Zlength rows ->
  prefix_match_z_29 (Znth k rows nil) prefix ->
  filter_prefix_state_29 rows prefix (k + 1) (out ++ [Znth k rows nil]).
Proof.
  intros rows prefix k out [Hbounds Hout] Hk Hmatch.
  split; [lia|].
  unfold filter_prefix_prefix_29 in *.
  rewrite firstn_succ_Z_29 by exact Hk.
  rewrite filter_prefix_rows_29_app.
  simpl.
  unfold prefix_match_z_29 in Hmatch.
  rewrite Hmatch.
  subst out.
  reflexivity.
Qed.

Lemma filter_prefix_prefix_29_step_skip : forall rows prefix k out,
  filter_prefix_state_29 rows prefix k out ->
  0 <= k < Zlength rows ->
  ~ prefix_match_z_29 (Znth k rows nil) prefix ->
  filter_prefix_state_29 rows prefix (k + 1) out.
Proof.
  intros rows prefix k out [Hbounds Hout] Hk Hnomatch.
  split; [lia|].
  unfold filter_prefix_prefix_29 in *.
  rewrite firstn_succ_Z_29 by exact Hk.
  rewrite filter_prefix_rows_29_app.
  simpl.
  destruct (String.prefix (string_of_list_z_29 prefix)
              (row_string_z_29 (Znth k rows nil))) eqn:Hpref.
  - exfalso; apply Hnomatch; exact Hpref.
  - rewrite app_nil_r.
    exact Hout.
Qed.

Lemma filter_prefix_rows_29_map : forall rows prefix,
  rows_to_strings_z_29 (filter_prefix_rows_29 rows prefix) =
  filter (fun s => String.prefix (string_of_list_z_29 prefix) s)
    (rows_to_strings_z_29 rows).
Proof.
  induction rows as [| row rest IH]; intros prefix; simpl.
  - reflexivity.
  - unfold rows_to_strings_z_29 in *; simpl in *.
    destruct (String.prefix (string_of_list_z_29 prefix) (row_string_z_29 row));
      simpl; rewrite IH; reflexivity.
Qed.

Lemma is_subsequence_cons_right_29 : forall (l : list string) x xs,
  is_subsequence l xs ->
  is_subsequence l (x :: xs).
Proof.
  destruct l as [| y ys]; simpl; intros x xs H.
  - exact I.
  - right; exact H.
Qed.

Lemma filter_is_subsequence_29 : forall (l : list string) p,
  is_subsequence (filter p l) l.
Proof.
  induction l as [| x xs IH]; simpl; intros p.
  - exact I.
  - destruct (p x) eqn:Hx.
    + left; split; [reflexivity| exact (IH p)].
    + apply is_subsequence_cons_right_29.
      exact (IH p).
Qed.

Lemma problem_29_spec_z_of_filter_state : forall rows prefix output_rows,
  filter_prefix_state_29 rows prefix (Zlength rows) output_rows ->
  problem_29_spec_z rows prefix output_rows.
Proof.
  intros rows prefix output_rows [_ Hout].
  unfold problem_29_spec_z, problem_29_spec.
  unfold filter_prefix_prefix_29 in Hout.
  rewrite firstn_all2 in Hout by (rewrite Zlength_correct; lia).
  subst output_rows.
  rewrite filter_prefix_rows_29_map.
  split.
  - apply filter_is_subsequence_29.
  - intro s.
    rewrite filter_In.
    reflexivity.
Qed.

Lemma ascii_of_z_29_inj_ascii : forall a b,
  0 <= a <= 127 ->
  0 <= b <= 127 ->
  ascii_of_z_29 a = ascii_of_z_29 b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  unfold ascii_of_z_29 in Heq.
  apply f_equal with (f := nat_of_ascii) in Heq.
  repeat rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.

Lemma string_prefix_true_of_z_eq_29 : forall prefix row,
  Zlength prefix <= Zlength row ->
  (forall k, 0 <= k < Zlength prefix -> Znth k row 0 = Znth k prefix 0) ->
  String.prefix (string_of_list_z_29 prefix) (string_of_list_z_29 row) = true.
Proof.
  induction prefix as [| pc ps IH]; intros row Hlen Heq; simpl.
  - destruct row; reflexivity.
  - destruct row as [| rc rs]; simpl in *.
    + rewrite Zlength_cons, Zlength_nil in Hlen.
      pose proof (Zlength_nonneg ps).
      lia.
    + rewrite !Zlength_cons in Hlen.
      assert (Hhead : rc = pc).
      {
        assert (H0 : 0 <= 0 < Zlength (pc :: ps)).
        { rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia. }
        specialize (Heq 0 H0).
        simpl in Heq.
        exact Heq.
      }
      subst rc.
      destruct (ascii_dec (ascii_of_z_29 pc) (ascii_of_z_29 pc)) as [_ | Hneq].
      * apply IH.
        -- lia.
        -- intros k Hk.
           specialize (Heq (k + 1)).
           rewrite !Znth_cons in Heq by lia.
           replace (k + 1 - 1) with k in Heq by lia.
           apply Heq.
           rewrite Zlength_cons.
           pose proof (Zlength_nonneg ps).
           lia.
      * contradiction.
Qed.

Lemma string_prefix_true_ascii_eq_29 : forall prefix row k,
  String.prefix (string_of_list_z_29 prefix) (string_of_list_z_29 row) = true ->
  0 <= k < Zlength prefix ->
  ascii_of_z_29 (Znth k prefix 0) = ascii_of_z_29 (Znth k row 0).
Proof.
  induction prefix as [| pc ps IH]; intros row k Hpref Hk; simpl in Hpref.
  - rewrite Zlength_nil in Hk; lia.
  - destruct row as [| rc rs]; simpl in Hpref.
    + discriminate.
    + rewrite Zlength_cons in Hk.
      destruct (ascii_dec (ascii_of_z_29 pc) (ascii_of_z_29 rc)) as [Heq | Hneq].
      * destruct (Z.eq_dec k 0) as [-> | Hnz].
        -- simpl. exact Heq.
        -- rewrite !Znth_cons by lia.
           apply IH; [exact Hpref | lia].
      * discriminate.
Qed.

Lemma string_prefix_true_length_29 : forall prefix row,
  String.prefix (string_of_list_z_29 prefix) (string_of_list_z_29 row) = true ->
  Zlength prefix <= Zlength row.
Proof.
  induction prefix as [| pc ps IH]; intros row Hpref.
  - rewrite Zlength_nil.
    apply Zlength_nonneg.
  - destruct row as [| rc rs]; simpl in Hpref.
    + discriminate.
    + destruct (ascii_dec (ascii_of_z_29 pc) (ascii_of_z_29 rc)) as [_ | Hneq];
        [| discriminate].
      rewrite !Zlength_cons.
      specialize (IH rs Hpref).
      lia.
Qed.

Lemma strncmp_result_prefix_match_29 : forall row prefix n ret,
  valid_string prefix ->
  n = string_length prefix ->
  strncmp_result (row_payload_z_29 row) prefix n ret ->
  ret = 0 ->
  prefix_match_z_29 row prefix.
Proof.
  intros row prefix n ret Hprefix_valid Hn Hcmp Hret.
  unfold strncmp_result in Hcmp.
  destruct Hcmp as [i [Hi0 [Hirow [Hiprefix [Heq Hcase]]]]].
  destruct Hcase as [[Hin Hret0] | [Hilt [Hret0 Hstop]]].
  - subst n ret.
    unfold prefix_match_z_29, row_string_z_29.
    apply string_prefix_true_of_z_eq_29.
    + unfold row_len_z_29, string_length in *.
      lia.
    + intros k Hk.
      assert (Hchars := Heq k).
      rewrite !c_string_Znth_inside in Hchars by (subst i; unfold string_length in *; lia).
      apply Hchars.
      subst i.
      unfold string_length in *.
      lia.
  - subst n ret.
    destruct Hstop as [Hzero | Hneq].
    + assert (Hprefix_zero : Znth i (c_string prefix) 0 = 0) by lia.
      rewrite c_string_Znth_inside in Hprefix_zero by (unfold string_length in *; lia).
      destruct Hprefix_valid as [_ Hno_nul].
      specialize (Hno_nul i ltac:(unfold string_length in *; lia)).
      contradiction.
    + lia.
Qed.

Lemma prefix_match_z_29_char_eq : forall row prefix k,
  valid_string (row_payload_z_29 row) ->
  valid_string prefix ->
  prefix_match_z_29 row prefix ->
  0 <= k < string_length prefix ->
  Znth k (c_string (row_payload_z_29 row)) 0 =
  Znth k (c_string prefix) 0.
Proof.
  intros row prefix k Hrow_valid Hprefix_valid Hpref Hk.
  unfold prefix_match_z_29, row_string_z_29 in Hpref.
  pose proof (string_prefix_true_length_29 prefix (row_payload_z_29 row) Hpref) as Hprefix_len.
  rewrite !c_string_Znth_inside by (unfold string_length in *; lia).
  assert (Hascii := string_prefix_true_ascii_eq_29 prefix (row_payload_z_29 row) k Hpref).
  assert (Hbounds : 0 <= k < Zlength prefix) by (unfold string_length in *; lia).
  specialize (Hascii Hbounds).
  destruct Hrow_valid as [Hrow_ascii _].
  destruct Hprefix_valid as [Hprefix_ascii _].
  apply ascii_of_z_29_inj_ascii.
  - apply Hrow_ascii.
    unfold string_length in *; lia.
  - apply Hprefix_ascii.
    unfold string_length in Hk; lia.
  - symmetry; exact Hascii.
Qed.

Lemma strncmp_result_prefix_nomatch_29 : forall row prefix n ret,
  valid_string (row_payload_z_29 row) ->
  valid_string prefix ->
  n = string_length prefix ->
  strncmp_result (row_payload_z_29 row) prefix n ret ->
  ret <> 0 ->
  ~ prefix_match_z_29 row prefix.
Proof.
  intros row prefix n ret Hrow_valid Hprefix_valid Hn Hcmp Hret Hpref.
  unfold strncmp_result in Hcmp.
  destruct Hcmp as [i [Hi0 [Hirow [Hiprefix [Heq Hcase]]]]].
  destruct Hcase as [[Hin Hzero] | [Hilt [Hret0 Hstop]]].
  - subst ret. contradiction.
  - subst n ret.
    assert (Hneq_chars :
      Znth i (c_string (row_payload_z_29 row)) 0 <>
      Znth i (c_string prefix) 0).
    {
      intro Hsame.
      lia.
    }
    apply Hneq_chars.
    apply prefix_match_z_29_char_eq; auto.
    unfold string_length in *; lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

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
