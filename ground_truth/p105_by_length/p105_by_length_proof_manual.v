Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p105_by_length Require Import p105_by_length_goal.
From SimpleC.EE.CAV.ground_truth_p105_by_length Require Import p105_by_length_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p105_by_length.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope Z_scope.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.



Lemma int_range_list_105_perm : forall a b,
  int_range_list_105 a ->
  Permutation a b ->
  int_range_list_105 b.
Proof.
  unfold int_range_list_105.
  intros a b Ha Hperm.
  eapply Permutation_Forall; eauto.
Qed.

Lemma int_range_list_105_Znth : forall l i,
  int_range_list_105 l ->
  0 <= i < Zlength l ->
  INT_MIN <= Znth i l 0 <= INT_MAX.
Proof.
  intros l i Hrange Hi.
  unfold int_range_list_105 in Hrange.
  apply Forall_forall with (x := Znth i l 0) in Hrange.
  - exact Hrange.
  - unfold Znth.
    apply nth_In.
    rewrite Zlength_correct in Hi.
    lia.
Qed.

Lemma copy_prefix_105_Zlength : forall input i,
  0 <= i <= Zlength input ->
  Zlength (copy_prefix_105 input i) = i.
Proof.
  intros input i Hi.
  unfold copy_prefix_105.
  rewrite Zlength_correct.
  rewrite sublist_length by lia.
  lia.
Qed.

Lemma copy_prefix_105_snoc : forall input i,
  0 <= i < Zlength input ->
  copy_prefix_105 input (i + 1) =
  copy_prefix_105 input i ++ [Znth i input 0].
Proof.
  intros input i Hi.
  unfold copy_prefix_105.
  rewrite (sublist_split 0 (i + 1) i input) by lia.
  rewrite (sublist_single 0 i input) by lia.
  reflexivity.
Qed.

Lemma Znth_In_range_105 : forall (l : list Z) i d,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros l i d Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Ltac destruct_digit_105 d Hd :=
  let Hcases := fresh "Hcases" in
  assert (d = 1 \/ d = 2 \/ d = 3 \/ d = 4 \/
          d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ d = 9) as Hcases by lia;
  repeat (destruct Hcases as [Hcases | Hcases];
          [subst d |]);
  [ idtac | idtac | idtac | idtac | idtac | idtac | idtac | idtac | subst d ].

Lemma digit_payload_ascii_105 : forall d c,
  1 <= d <= 9 ->
  In c (digit_payload_105 d) ->
  0 <= c <= 127.
Proof.
  intros d c Hd Hin.
  destruct_digit_105 d Hd;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma digit_payload_nonzero_105 : forall d c,
  1 <= d <= 9 ->
  In c (digit_payload_105 d) ->
  c <> 0.
Proof.
  intros d c Hd Hin.
  destruct_digit_105 d Hd;
    vm_compute in Hin;
    repeat (destruct Hin as [Hin | Hin]; [subst; lia |]);
    contradiction.
Qed.

Lemma digit_payload_valid_string_105 : forall d,
  1 <= d <= 9 ->
  string_lib.valid_string (digit_payload_105 d).
Proof.
  intros d Hd.
  unfold string_lib.valid_string, string_lib.all_ascii, string_lib.no_inner_nul.
  split; intros i Hi;
    pose proof (Znth_In_range_105 (digit_payload_105 d) i 0 Hi) as Hin.
  - apply digit_payload_ascii_105 with (d := d); assumption.
  - apply digit_payload_nonzero_105 with (d := d); assumption.
Qed.

Lemma digit_payload_length_bound_105 : forall d,
  1 <= d <= 9 ->
  string_lib.string_length (digit_payload_105 d) < INT_MAX.
Proof.
  intros d Hd.
  destruct_digit_105 d Hd;
    unfold string_lib.string_length, digit_payload_105, lit_payload_105,
      digit_literal_105;
    unfold one_literal_105, two_literal_105, three_literal_105,
      four_literal_105, five_literal_105, six_literal_105,
      seven_literal_105, eight_literal_105, nine_literal_105;
    rewrite StringToList_length;
    unfold StringLength; simpl; lia.
Qed.

Lemma digit_payloads_string_safe_105_proof :
  digit_payloads_string_safe_105.
Proof.
  unfold digit_payloads_string_safe_105.
  repeat split;
    try solve
      [ apply digit_payload_valid_string_105; lia
      | apply digit_payload_length_bound_105; lia ].
Qed.

Lemma target_digit_105_true : forall d,
  1 <= d <= 9 ->
  target_digit_105 d = true.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_true_iff.
  split; apply Z.leb_le; lia.
Qed.

Lemma target_digit_105_false_high : forall d,
  d > 9 ->
  target_digit_105 d = false.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_false_iff.
  right.
  apply Z.leb_gt.
  lia.
Qed.

Lemma target_digit_105_false_low : forall d,
  d < 1 ->
  target_digit_105 d = false.
Proof.
  intros d Hd.
  unfold target_digit_105.
  apply andb_false_iff.
  left.
  apply Z.leb_gt.
  lia.
Qed.

Lemma filtered_rev_sublist_skip_step_105 : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - (k + 1)) (Zlength sorted_l) sorted_l)) =
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - k) (Zlength sorted_l) sorted_l)).
Proof.
  intros sorted_l k d Hk Hd Htarget.
  replace (Zlength sorted_l - (k + 1)) with (Zlength sorted_l - 1 - k) by lia.
  replace (Zlength sorted_l - k) with (Zlength sorted_l - 1 - k + 1) by lia.
  rewrite (sublist_split (Zlength sorted_l - 1 - k)
    (Zlength sorted_l) (Zlength sorted_l - 1 - k + 1) sorted_l) by lia.
  rewrite (sublist_single 0 (Zlength sorted_l - 1 - k) sorted_l) by lia.
  rewrite <- Hd.
  rewrite rev_app_distr.
  simpl.
  rewrite filter_app.
  simpl.
  rewrite Htarget.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma filtered_rev_sublist_hit_step_105 : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - (k + 1)) (Zlength sorted_l) sorted_l)) =
  filter target_digit_105
    (rev (sublist (Zlength sorted_l - k) (Zlength sorted_l) sorted_l)) ++ [d].
Proof.
  intros sorted_l k d Hk Hd Htarget.
  replace (Zlength sorted_l - (k + 1)) with (Zlength sorted_l - 1 - k) by lia.
  replace (Zlength sorted_l - k) with (Zlength sorted_l - 1 - k + 1) by lia.
  rewrite (sublist_split (Zlength sorted_l - 1 - k)
    (Zlength sorted_l) (Zlength sorted_l - 1 - k + 1) sorted_l) by lia.
  rewrite (sublist_single 0 (Zlength sorted_l - 1 - k) sorted_l) by lia.
  rewrite <- Hd.
  rewrite rev_app_distr.
  simpl.
  rewrite filter_app.
  simpl.
  rewrite Htarget.
  reflexivity.
Qed.

Lemma digit_words_between_105_skip_step : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  digit_words_between_105 sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l).
Proof.
  intros sorted_l k d Hk Hd Htarget.
  unfold digit_words_between_105.
  rewrite (filtered_rev_sublist_skip_step_105 sorted_l k d) by auto.
  reflexivity.
Qed.

Lemma digit_ptrs_between_105_skip_step : forall LM sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l).
Proof.
  intros LM sorted_l k d Hk Hd Htarget.
  unfold digit_ptrs_between_105.
  rewrite (filtered_rev_sublist_skip_step_105 sorted_l k d) by auto.
  reflexivity.
Qed.

Lemma digit_words_between_105_hit_step : forall sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  digit_words_between_105 sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_words_between_105 sorted_l (Zlength sorted_l - k) (Zlength sorted_l) ++
    [digit_payload_105 d].
Proof.
  intros sorted_l k d Hk Hd Htarget.
  unfold digit_words_between_105.
  rewrite (filtered_rev_sublist_hit_step_105 sorted_l k d) by auto.
  rewrite map_app.
  reflexivity.
Qed.

Lemma digit_ptrs_between_105_hit_step : forall LM sorted_l k d,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - (k + 1)) (Zlength sorted_l) =
  digit_ptrs_between_105 LM sorted_l (Zlength sorted_l - k) (Zlength sorted_l) ++
    [digit_ptr_105 LM d].
Proof.
  intros LM sorted_l k d Hk Hd Htarget.
  unfold digit_ptrs_between_105.
  rewrite (filtered_rev_sublist_hit_step_105 sorted_l k d) by auto.
  rewrite map_app.
  reflexivity.
Qed.

Lemma output_state_105_skip_step : forall LM sorted_l k d rows ptrs,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = false ->
  output_state_105 LM sorted_l k rows ptrs ->
  output_state_105 LM sorted_l (k + 1) rows ptrs.
Proof.
  intros LM sorted_l k d rows ptrs Hk Hd Htarget Hstate.
  destruct Hstate as [Hkbounds [Hrows Hptrs]].
  unfold output_state_105.
  repeat split; try lia.
  - rewrite Hrows.
    symmetry.
    apply (digit_words_between_105_skip_step sorted_l k d); assumption.
  - rewrite Hptrs.
    symmetry.
    apply (digit_ptrs_between_105_skip_step LM sorted_l k d); assumption.
Qed.

Lemma output_state_105_hit_step : forall LM sorted_l k d rows ptrs,
  0 <= k < Zlength sorted_l ->
  d = Znth (Zlength sorted_l - 1 - k) sorted_l 0 ->
  target_digit_105 d = true ->
  output_state_105 LM sorted_l k rows ptrs ->
  output_state_105 LM sorted_l (k + 1)
    (rows ++ [digit_payload_105 d]) (ptrs ++ [digit_ptr_105 LM d]).
Proof.
  intros LM sorted_l k d rows ptrs Hk Hd Htarget Hstate.
  destruct Hstate as [Hkbounds [Hrows Hptrs]].
  unfold output_state_105.
  repeat split; try lia.
  - rewrite Hrows.
    symmetry.
    apply (digit_words_between_105_hit_step sorted_l k d); assumption.
  - rewrite Hptrs.
    symmetry.
    apply (digit_ptrs_between_105_hit_step LM sorted_l k d); assumption.
Qed.

Lemma target_digit_105_is_target_digit : forall d,
  target_digit_105 d = is_target_digit d.
Proof.
  intros d.
  unfold target_digit_105, is_target_digit.
  reflexivity.
Qed.

Lemma target_digit_105_true_range : forall d,
  target_digit_105 d = true ->
  1 <= d <= 9.
Proof.
  intros d Htarget.
  unfold target_digit_105 in Htarget.
  apply andb_true_iff in Htarget.
  destruct Htarget as [Hlow Hhigh].
  split; apply Z.leb_le; assumption.
Qed.

Lemma digit_payload_to_word_105 : forall d,
  1 <= d <= 9 ->
  string_of_list_z_105 (digit_payload_105 d) = digit_to_word d.
Proof.
  intros d Hd.
  destruct_digit_105 d Hd; vm_compute; reflexivity.
Qed.

Lemma filter_rev_target_105 : forall l,
  filter target_digit_105 (rev l) = rev (filter target_digit_105 l).
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite filter_app.
    rewrite IH.
    destruct (target_digit_105 x) eqn:Htx; simpl.
    + rewrite Htx. reflexivity.
    + rewrite Htx. rewrite app_nil_r. reflexivity.
Qed.

Lemma Permutation_filter_target_105 : forall l1 l2,
  Permutation l1 l2 ->
  Permutation (filter target_digit_105 l1) (filter target_digit_105 l2).
Proof.
  intros l1 l2 Hperm.
  induction Hperm.
  - constructor.
  - simpl.
    destruct (target_digit_105 x).
    + constructor; assumption.
    + assumption.
  - simpl.
    destruct (target_digit_105 x);
      destruct (target_digit_105 y);
      try apply perm_swap;
      reflexivity.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma Forall_filter_target_105 : forall (P : Z -> Prop) l,
  Forall P l ->
  Forall P (filter target_digit_105 l).
Proof.
  intros P l Hforall.
  apply Forall_forall.
  intros x Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin _].
  apply Forall_forall with (x := x) in Hforall; assumption.
Qed.

Lemma StronglySorted_filter_target_105 : forall l,
  StronglySorted Z.le l ->
  StronglySorted Z.le (filter target_digit_105 l).
Proof.
  intros l Hsorted.
  induction Hsorted.
  - constructor.
  - simpl.
    destruct (target_digit_105 a).
    + constructor.
      * assumption.
      * apply Forall_filter_target_105; assumption.
    + assumption.
Qed.

Lemma Sorted_filter_target_105 : forall l,
  Sorted Z.le l ->
  Sorted Z.le (filter target_digit_105 l).
Proof.
  intros l Hsorted.
  apply StronglySorted_Sorted.
  apply StronglySorted_filter_target_105.
  apply Sorted_StronglySorted.
  - intros x y z Hxy Hyz; lia.
  - exact Hsorted.
Qed.

Lemma map_digit_payload_words_Forall_105 : forall l,
  Forall (fun d => 1 <= d <= 9) l ->
  map string_of_list_z_105 (map digit_payload_105 l) =
  map digit_to_word l.
Proof.
  intros l Hrange.
  induction Hrange; simpl.
  - reflexivity.
  - rewrite digit_payload_to_word_105 by assumption.
    rewrite IHHrange.
    reflexivity.
Qed.

Lemma Forall_rev_filter_target_range_105 : forall l,
  Forall (fun d => 1 <= d <= 9) (rev (filter target_digit_105 l)).
Proof.
  intros l.
  apply Forall_forall.
  intros d Hin.
  apply in_rev in Hin.
  apply filter_In in Hin.
  destruct Hin as [_ Htarget].
  apply target_digit_105_true_range.
  exact Htarget.
Qed.

Lemma problem_105_spec_z_of_output_state_intro : forall input sorted_l output_rows LM output_ptrs,
  sorted_int_list_by 1 sorted_l ->
  Permutation input sorted_l ->
  output_rows = digit_words_between_105 sorted_l 0 (Zlength sorted_l) ->
  output_ptrs = digit_ptrs_between_105 LM sorted_l 0 (Zlength sorted_l) ->
  problem_105_spec_z input output_rows.
Proof.
  intros input sorted_l output_rows LM output_ptrs Hsorted Hperm Hrows _.
  unfold problem_105_spec_z, problem_105_spec.
  exists (filter is_target_digit sorted_l).
  split.
  - split.
    + replace (filter is_target_digit input)
        with (filter target_digit_105 input)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      replace (filter is_target_digit sorted_l)
        with (filter target_digit_105 sorted_l)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      apply Permutation_filter_target_105.
      exact Hperm.
    + replace (filter is_target_digit sorted_l)
        with (filter target_digit_105 sorted_l)
        by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
      unfold sorted_int_list_by in Hsorted.
      simpl in Hsorted.
      apply Sorted_filter_target_105.
      exact Hsorted.
  - subst output_rows.
    unfold digit_words_between_105.
    rewrite sublist_self by (pose proof (Zlength_nonneg sorted_l); lia).
    rewrite filter_rev_target_105.
    replace (filter is_target_digit sorted_l)
      with (filter target_digit_105 sorted_l)
      by (apply filter_ext; intros; symmetry; apply target_digit_105_is_target_digit).
    apply map_digit_payload_words_Forall_105.
    apply Forall_rev_filter_target_range_105.
Qed.

Lemma one_lit_to_store_105 : forall LM,
  store_stringLit (LM one_literal_105) one_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 1) (digit_payload_105 1).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, one_literal_105.
  simpl. entailer!.
Qed.

Lemma two_lit_to_store_105 : forall LM,
  store_stringLit (LM two_literal_105) two_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 2) (digit_payload_105 2).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, two_literal_105.
  simpl. entailer!.
Qed.

Lemma three_lit_to_store_105 : forall LM,
  store_stringLit (LM three_literal_105) three_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 3) (digit_payload_105 3).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, three_literal_105.
  simpl. entailer!.
Qed.

Lemma four_lit_to_store_105 : forall LM,
  store_stringLit (LM four_literal_105) four_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 4) (digit_payload_105 4).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, four_literal_105.
  simpl. entailer!.
Qed.

Lemma five_lit_to_store_105 : forall LM,
  store_stringLit (LM five_literal_105) five_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 5) (digit_payload_105 5).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, five_literal_105.
  simpl. entailer!.
Qed.

Lemma six_lit_to_store_105 : forall LM,
  store_stringLit (LM six_literal_105) six_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 6) (digit_payload_105 6).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, six_literal_105.
  simpl. entailer!.
Qed.

Lemma seven_lit_to_store_105 : forall LM,
  store_stringLit (LM seven_literal_105) seven_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 7) (digit_payload_105 7).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, seven_literal_105.
  simpl. entailer!.
Qed.

Lemma eight_lit_to_store_105 : forall LM,
  store_stringLit (LM eight_literal_105) eight_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 8) (digit_payload_105 8).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, eight_literal_105.
  simpl. entailer!.
Qed.

Lemma nine_lit_to_store_105 : forall LM,
  store_stringLit (LM nine_literal_105) nine_literal_105 |--
  string_lib.store_string (digit_ptr_105 LM 9) (digit_payload_105 9).
Proof.
  intros.
  unfold store_stringLit, string_lib.store_string.
  unfold digit_ptr_105, digit_payload_105, digit_literal_105, lit_payload_105, nine_literal_105.
  simpl. entailer!.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_105 :=
  pre_process_default;
  subst;
  entailer!.

Lemma ptrarray_snoc_undef_105 : forall data ptrs ptr cap,
  Zlength ptrs < cap ->
  PtrArray.seg data 0 (Zlength ptrs + 1) (ptrs ++ cons ptr (@nil Z)) **
  PtrArray.undef_missing_i data (Zlength ptrs) (Zlength ptrs) cap
  |--
  PtrArray.seg data 0 (Zlength (ptrs ++ cons ptr (@nil Z)))
    (ptrs ++ cons ptr (@nil Z)) **
  PtrArray.undef_seg data (Zlength (ptrs ++ cons ptr (@nil Z))) cap.
Proof.
  intros data ptrs ptr cap Hcap.
  replace (Zlength (ptrs ++ cons ptr (@nil Z)))
    with (Zlength ptrs + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  apply derivable1_sepcon_mono.
  - apply derivable1_refl.
  - apply PtrArray.undef_missing_i_to_undef_seg_head.
    exact Hcap.
Qed.

Lemma ptrarray_snoc_undef_frame_105 : forall data ptrs ptr cap R,
  Zlength ptrs < cap ->
  PtrArray.seg data 0 (Zlength ptrs + 1) (ptrs ++ cons ptr (@nil Z)) **
    (PtrArray.undef_missing_i data (Zlength ptrs) (Zlength ptrs) cap ** R)
  |--
  (PtrArray.seg data 0 (Zlength ptrs + 1)
    (ptrs ++ cons ptr (@nil Z)) **
   PtrArray.undef_seg data (Zlength ptrs + 1) cap) ** R.
Proof.
  intros data ptrs ptr cap R Hcap.
  eapply derivable1_trans.
  - apply derivable1_sepcon_assoc1.
  - apply derivable1_sepcon_mono.
    + apply derivable1_sepcon_mono.
      * apply derivable1_refl.
      * apply PtrArray.undef_missing_i_to_undef_seg_head.
        exact Hcap.
    + apply derivable1_refl.
Qed.

Ltac prove_digit_hit_105 dval ptr :=
  right;
  pre_process_default;
  match goal with
  | i : Z, sorted_l_2 : list Z, output_rows_2 : list (list Z),
    output_ptrs_2 : list Z, k : Z, out_size : Z, data : Z,
    arr_size_pre : Z |- _ =>
      assert (Hdigit_value_105 : Znth i sorted_l_2 0 = dval) by lia;
      Exists (output_rows_2 ++ cons (digit_payload_105 dval) (@nil (list Z)));
      assert (Htarget_105 : target_digit_105 dval = true)
        by (apply target_digit_105_true; lia);
      assert (Hstep_105 : output_state_105 LitMap sorted_l_2 (k + 1)
        (output_rows_2 ++ cons (digit_payload_105 dval) (@nil (list Z)))
        (output_ptrs_2 ++ cons (digit_ptr_105 LitMap dval) (@nil Z)));
      [ eapply output_state_105_hit_step with (d := dval);
        try eassumption; try lia;
        rewrite <- Hdigit_value_105; f_equal; lia
      | ];
      match goal with
      | Hptr : ptr = digit_ptr_105 LitMap dval |- _ => rewrite <- Hptr in *
      end;
      match goal with
      | Hout : out_size = Zlength output_ptrs_2 |- _ => rewrite Hout in *
      end;
      destruct Hstep_105 as [Hkstep_105 [Hrowsstep_105 Hptrsstep_105]];
      match goal with
      | Harr : arr_size_pre = Zlength sorted_l_2 |- _ =>
          assert (Hptrs_goal_105 :
            output_ptrs_2 ++ cons ptr (@nil Z) =
            digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
              arr_size_pre)
          by (rewrite Hptrsstep_105; rewrite Harr; reflexivity)
      end;
      assert (Hstate_goal_105 :
        output_state_105 LitMap sorted_l_2 (k + 1)
          (output_rows_2 ++ cons (digit_payload_105 dval) (@nil (list Z)))
          (output_ptrs_2 ++ cons ptr (@nil Z)));
      [ unfold output_state_105;
        repeat split; try lia;
        [ exact Hrowsstep_105 | exact Hptrsstep_105 ]
      | ];
      match goal with
      | Hpg : output_ptrs_2 ++ cons ptr (@nil Z) =
          digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
            arr_size_pre |- _ =>
          rewrite <- Hpg in *
      end;
      rewrite Zlength_app;
      rewrite Zlength_cons;
      rewrite Zlength_nil;
      replace (Zlength (output_ptrs_2 ++ cons ptr (@nil Z)))
        with (Zlength output_ptrs_2 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
      replace (Zlength (output_rows_2 ++ cons (digit_payload_105 dval) (@nil (list Z))))
        with (Zlength output_rows_2 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
      apply split_pure_and_spatial_goals;
      [ apply ptrarray_snoc_undef_frame_105; lia
      | split_pures;
        try solve [dump_pre_spatial; assumption
                 | dump_pre_spatial; lia
                 | dump_pre_spatial; reflexivity] ]
  end.

Ltac finish_digit_hit_named_105
    dval ptr n sorted rows ptrs idx kk Hptr Harr Hout :=
  assert (Hdigit_value_105 : Znth idx sorted 0 = dval) by lia;
  Exists (rows ++ cons (digit_payload_105 dval) (@nil (list Z)));
  assert (Htarget_105 : target_digit_105 dval = true)
    by (apply target_digit_105_true; lia);
  assert (Hstep_105 : output_state_105 LitMap sorted (kk + 1)
    (rows ++ cons (digit_payload_105 dval) (@nil (list Z)))
    (ptrs ++ cons (digit_ptr_105 LitMap dval) (@nil Z)));
  [ eapply output_state_105_hit_step with (d := dval);
    try eassumption; try lia;
    rewrite <- Hdigit_value_105; f_equal; lia
  | ];
  rewrite <- Hptr in *;
  rewrite Hout in *;
  destruct Hstep_105 as [Hkstep_105 [Hrowsstep_105 Hptrsstep_105]];
  assert (Hptrs_goal_105 :
    ptrs ++ cons ptr (@nil Z) =
    digit_ptrs_between_105 LitMap sorted (n - (kk + 1)) n)
  by (rewrite Hptrsstep_105; try rewrite Harr; reflexivity);
  assert (Hstate_goal_105 :
    output_state_105 LitMap sorted (kk + 1)
      (rows ++ cons (digit_payload_105 dval) (@nil (list Z)))
      (ptrs ++ cons ptr (@nil Z)));
  [ unfold output_state_105;
    repeat split; try lia;
    [ exact Hrowsstep_105 | exact Hptrsstep_105 ]
  | ];
  rewrite <- Hptrs_goal_105 in *;
  rewrite Zlength_app;
  rewrite Zlength_cons;
  rewrite Zlength_nil;
  replace (Zlength (ptrs ++ cons ptr (@nil Z)))
    with (Zlength ptrs + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
  replace (Zlength (rows ++ cons (digit_payload_105 dval) (@nil (list Z))))
    with (Zlength rows + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
  apply split_pure_and_spatial_goals;
  [ apply ptrarray_snoc_undef_frame_105; lia
  | split_pures;
    try solve [dump_pre_spatial; assumption
             | dump_pre_spatial; lia
             | dump_pre_spatial; reflexivity] ].

Lemma proof_of_by_length_entail_wit_1 : by_length_entail_wit_1.
Proof.
  left.
  pre_process_default.
  pose proof digit_payloads_string_safe_105_proof as Hdigit_payloads_string_safe_105.
  unfold digit_literals_heap_105.
  sep_apply_l_atomic (one_lit_to_store_105 LitMap).
  sep_apply_l_atomic (two_lit_to_store_105 LitMap).
  sep_apply_l_atomic (three_lit_to_store_105 LitMap).
  sep_apply_l_atomic (four_lit_to_store_105 LitMap).
  sep_apply_l_atomic (five_lit_to_store_105 LitMap).
  sep_apply_l_atomic (six_lit_to_store_105 LitMap).
  sep_apply_l_atomic (seven_lit_to_store_105 LitMap).
  sep_apply_l_atomic (eight_lit_to_store_105 LitMap).
  sep_apply_l_atomic (nine_lit_to_store_105 LitMap).
  unfold all_digit_literals_105.
  unfold digit_ptr_105, digit_literal_105.
  unfold one_literal_105, two_literal_105, three_literal_105,
    four_literal_105, five_literal_105, six_literal_105,
    seven_literal_105, eight_literal_105, nine_literal_105.
  simpl.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_2 : by_length_entail_wit_2.
Proof.
  left.
  pre_process_default.
  Exists (@nil Z).
  unfold copy_prefix_105.
  sep_apply IntArray.undef_full_to_undef_seg.
  rewrite (IntArray.seg_empty retval_3 0).
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_3 : by_length_entail_wit_3.
Proof.
  left.
  pre_process_default.
  Exists (tmp_l_2 +:: Znth i input_l 0).
  rewrite PreH24.
  rewrite copy_prefix_105_snoc by lia.
  rewrite Zlength_app.
  rewrite copy_prefix_105_Zlength by lia.
  simpl.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_4 : by_length_entail_wit_4.
Proof.
  left.
  pre_process_default.
  assert (Hlen_eq : Zlength tmp_l = Zlength input_l) by lia.
  rewrite Hlen_eq in *.
  assert (Htmp_eq : tmp_l = input_l).
  {
    rewrite PreH24.
    unfold copy_prefix_105.
    rewrite sublist_self by lia.
    reflexivity.
  }
  assert (Hi_eq : i = arr_size_pre) by lia.
  subst i.
  rewrite Htmp_eq.
  rewrite Hi_eq.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_5 : by_length_entail_wit_5.
Proof.
  left.
  pre_process_default.
  assert (Hsorted_full : sorted_full_l = sorted_l_2).
  {
    rewrite <- PreH7.
    rewrite sublist_self by lia.
    reflexivity.
  }
  subst sorted_full_l.
  destruct PreH27 as [Hinput_pre Hinput_range].
  pose proof (int_range_list_105_perm input_l sorted_l_2 Hinput_range PreH9)
    as Hsorted_range.
  assert (Hprez : problem_105_pre_z input_l) by (split; assumption).
  Exists sorted_l_2.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_6 : by_length_entail_wit_6.
Proof.
  left.
  pre_process_default.
  subst out_size.
  Exists (@nil (list Z)) (@nil Z) sorted_l_2.
  sep_apply PtrArray.undef_full_to_undef_seg.
  rewrite (PtrArray.seg_empty data 0).
  unfold output_state_105, digit_words_between_105, digit_ptrs_between_105.
  replace (arr_size_pre - 0) with arr_size_pre by lia.
  replace (Zlength sorted_l_2 - 0) with (Zlength sorted_l_2) by lia.
  replace (sublist arr_size_pre arr_size_pre sorted_l_2) with (@nil Z)
    by (symmetry; apply sublist_nil; lia).
  replace (sublist (Zlength sorted_l_2) (Zlength sorted_l_2) sorted_l_2)
    with (@nil Z) by (symmetry; apply sublist_nil; lia).
  simpl.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_7 : by_length_entail_wit_7.
Proof.
  left.
  pre_process_default.
  pose proof (int_range_list_105_Znth sorted_l_2
    (arr_size_pre - 1 - k) PreH22) as Hrange_z.
  assert (Hidx_bounds : 0 <= arr_size_pre - 1 - k < Zlength sorted_l_2) by lia.
  specialize (Hrange_z Hidx_bounds).
  Exists output_rows_2
    (digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - k) arr_size_pre)
    sorted_l_2.
  rewrite PreH31 in *.
  sep_apply_l_atomic (IntArray.full_split_to_missing_i tmp
    (arr_size_pre - 1 - k) arr_size_pre sorted_l_2 0).
  { entailer!. }
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_8 : by_length_entail_wit_8.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2
    (digit_ptrs_between_105 LitMap sorted_l (arr_size_pre - k) arr_size_pre)
    sorted_l.
  rewrite PreH37 in *.
  sep_apply_l_atomic (IntArray.missing_i_merge_to_full tmp
    i arr_size_pre (Znth i sorted_l 0) sorted_l).
  { entailer!. }
  rewrite replace_Znth_Znth by lia.
  rewrite PreH29 in *.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_9_1 : by_length_entail_wit_9_1.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2 output_ptrs_2 sorted_l_2.
  assert (Htarget : target_digit_105 d = false)
    by (apply target_digit_105_false_high; lia).
  assert (Hstep : output_state_105 LitMap sorted_l_2 (k + 1)
    output_rows_2 output_ptrs_2).
  {
    eapply output_state_105_skip_step with (d := d); try eassumption; try lia.
    rewrite PreH38.
    f_equal.
    lia.
  }
  destruct Hstep as [Hkstep [Hrowsstep Hptrsstep]].
  assert (Hptrs_goal :
    output_ptrs_2 =
    digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
      arr_size_pre).
  {
    rewrite Hptrsstep.
    rewrite PreH19.
    reflexivity.
  }
  assert (Hstate_goal :
    output_state_105 LitMap sorted_l_2 (k + 1) output_rows_2 output_ptrs_2).
  {
    unfold output_state_105.
    repeat split; try lia.
    - exact Hrowsstep.
    - exact Hptrsstep.
  }
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_9_2 : by_length_entail_wit_9_2.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2 output_ptrs_2 sorted_l_2.
  assert (Htarget : target_digit_105 d = false)
    by (apply target_digit_105_false_low; lia).
  assert (Hstep : output_state_105 LitMap sorted_l_2 (k + 1)
    output_rows_2 output_ptrs_2).
  {
    eapply output_state_105_skip_step with (d := d); try eassumption; try lia.
    rewrite PreH37.
    f_equal.
    lia.
  }
  destruct Hstep as [Hkstep [Hrowsstep Hptrsstep]].
  assert (Hptrs_goal :
    output_ptrs_2 =
    digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
      arr_size_pre).
  {
    rewrite Hptrsstep.
    rewrite PreH18.
    reflexivity.
  }
  assert (Hstate_goal :
    output_state_105 LitMap sorted_l_2 (k + 1) output_rows_2 output_ptrs_2).
  {
    unfold output_state_105.
    repeat split; try lia.
    - exact Hrowsstep.
    - exact Hptrsstep.
  }
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_9_3 : by_length_entail_wit_9_3.
Proof.
  right.
  pre_process_default.
  assert (Hd9 : Znth i sorted_l_2 0 = 9) by lia.
  Exists (output_rows_2 ++ cons (digit_payload_105 9) (@nil (list Z))).
  assert (Htarget : target_digit_105 9 = true)
    by (apply target_digit_105_true; lia).
  assert (Hstep : output_state_105 LitMap sorted_l_2 (k + 1)
    (output_rows_2 ++ cons (digit_payload_105 9) (@nil (list Z)))
    (output_ptrs_2 ++ cons (digit_ptr_105 LitMap 9) (@nil Z))).
  {
    eapply output_state_105_hit_step with (d := 9); try eassumption; try lia.
    rewrite <- Hd9.
    f_equal.
    lia.
  }
  rewrite <- PreH19 in *.
  rewrite PreH42 in *.
  destruct Hstep as [Hkstep [Hrowsstep Hptrsstep]].
  assert (Hptrs_goal :
    output_ptrs_2 ++ cons nine (@nil Z) =
    digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
      arr_size_pre).
  {
    rewrite Hptrsstep.
    rewrite PreH27.
    reflexivity.
  }
  assert (Hstate_goal :
    output_state_105 LitMap sorted_l_2 (k + 1)
      (output_rows_2 ++ cons (digit_payload_105 9) (@nil (list Z)))
      (output_ptrs_2 ++ cons nine (@nil Z))).
  {
    unfold output_state_105.
    repeat split; try lia.
    - exact Hrowsstep.
    - exact Hptrsstep.
  }
  rewrite <- Hptrs_goal in *.
  rewrite Zlength_app.
  rewrite Zlength_cons.
  rewrite Zlength_nil.
  replace (Zlength (output_ptrs_2 ++ cons nine (@nil Z)))
    with (Zlength output_ptrs_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  replace (Zlength (output_rows_2 ++ cons (digit_payload_105 9) (@nil (list Z))))
    with (Zlength output_rows_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  apply split_pure_and_spatial_goals.
  - apply ptrarray_snoc_undef_frame_105.
    lia.
  - split_pures;
    try solve [dump_pre_spatial; assumption
             | dump_pre_spatial; lia
             | dump_pre_spatial; reflexivity].
Qed.

Lemma proof_of_by_length_entail_wit_9_4 : by_length_entail_wit_9_4.
Proof.
  right.
  pre_process_default.
  assert (Hd8 : Znth i sorted_l_2 0 = 8) by lia.
  Exists (output_rows_2 ++ cons (digit_payload_105 8) (@nil (list Z))).
  assert (Htarget : target_digit_105 8 = true)
    by (apply target_digit_105_true; lia).
  assert (Hstep : output_state_105 LitMap sorted_l_2 (k + 1)
    (output_rows_2 ++ cons (digit_payload_105 8) (@nil (list Z)))
    (output_ptrs_2 ++ cons (digit_ptr_105 LitMap 8) (@nil Z))).
  {
    eapply output_state_105_hit_step with (d := 8); try eassumption; try lia.
    rewrite <- Hd8.
    f_equal.
    lia.
  }
  rewrite <- PreH18 in *.
  rewrite PreH42 in *.
  destruct Hstep as [Hkstep [Hrowsstep Hptrsstep]].
  assert (Hptrs_goal :
    output_ptrs_2 ++ cons eight (@nil Z) =
    digit_ptrs_between_105 LitMap sorted_l_2 (arr_size_pre - (k + 1))
      arr_size_pre).
  {
    rewrite Hptrsstep.
    rewrite PreH27.
    reflexivity.
  }
  assert (Hstate_goal :
    output_state_105 LitMap sorted_l_2 (k + 1)
      (output_rows_2 ++ cons (digit_payload_105 8) (@nil (list Z)))
      (output_ptrs_2 ++ cons eight (@nil Z))).
  {
    unfold output_state_105.
    repeat split; try lia.
    - exact Hrowsstep.
    - exact Hptrsstep.
  }
  rewrite <- Hptrs_goal in *.
  rewrite Zlength_app.
  rewrite Zlength_cons.
  rewrite Zlength_nil.
  replace (Zlength (output_ptrs_2 ++ cons eight (@nil Z)))
    with (Zlength output_ptrs_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  replace (Zlength (output_rows_2 ++ cons (digit_payload_105 8) (@nil (list Z))))
    with (Zlength output_rows_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  apply split_pure_and_spatial_goals.
  - apply ptrarray_snoc_undef_frame_105.
    lia.
  - split_pures;
    try solve [dump_pre_spatial; assumption
             | dump_pre_spatial; lia
             | dump_pre_spatial; reflexivity].
Qed.

Lemma proof_of_by_length_entail_wit_9_5 : by_length_entail_wit_9_5.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 7 seven arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH16 PreH26 PreH41.
Qed.

Lemma proof_of_by_length_entail_wit_9_6 : by_length_entail_wit_9_6.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 6 six arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH14 PreH25 PreH40.
Qed.

Lemma proof_of_by_length_entail_wit_9_7 : by_length_entail_wit_9_7.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 5 five arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH12 PreH24 PreH39.
Qed.

Lemma proof_of_by_length_entail_wit_9_8 : by_length_entail_wit_9_8.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 4 four arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH10 PreH23 PreH38.
Qed.

Lemma proof_of_by_length_entail_wit_9_9 : by_length_entail_wit_9_9.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 3 three arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH8 PreH22 PreH37.
Qed.

Lemma proof_of_by_length_entail_wit_9_10 : by_length_entail_wit_9_10.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 2 two arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH6 PreH21 PreH36.
Qed.

Lemma proof_of_by_length_entail_wit_9_11 : by_length_entail_wit_9_11.
Proof.
  right.
  pre_process_default.
  finish_digit_hit_named_105 1 one arr_size_pre sorted_l_2
    output_rows_2 output_ptrs_2 i k PreH4 PreH20 PreH35.
Qed.

Lemma proof_of_by_length_entail_wit_10 : by_length_entail_wit_10.
Proof.
  left.
  pre_process_default.
  Exists output_rows_2 output_ptrs_2 sorted_l_2.
  entailer!.
Qed.

Lemma proof_of_by_length_entail_wit_11 : by_length_entail_wit_11.
Proof.
  left.
  pre_process_default.
  assert (Hk_eq : k = arr_size_pre) by lia.
  subst k.
  Exists output_rows_2 output_ptrs_2 sorted_l_2.
  assert (Hspec_state :
    problem_105_spec_z_of_output_state input_l sorted_l_2
      output_rows_2 LitMap output_ptrs_2).
  {
    unfold problem_105_spec_z_of_output_state.
    intros Hsorted Hperm Hrows Hptrs.
    eapply problem_105_spec_z_of_output_state_intro; eauto.
  }
  entailer!.
Qed.

Lemma proof_of_by_length_return_wit_1 : by_length_return_wit_1.
Proof.
  left.
  pre_process_default.
  destruct PreH21 as [Hkbounds [Hrows Hptrs]].
  assert (Hrows0 :
    output_rows_2 = digit_words_between_105 sorted_l 0 (Zlength sorted_l)).
  {
    rewrite Hrows.
    replace (Zlength sorted_l - arr_size_pre) with 0 by lia.
    reflexivity.
  }
  assert (Hptrs0 :
    output_ptrs_2 = digit_ptrs_between_105 LitMap sorted_l 0 (Zlength sorted_l)).
  {
    rewrite Hptrs.
    replace (Zlength sorted_l - arr_size_pre) with 0 by lia.
    reflexivity.
  }
  assert (Hspec : problem_105_spec_z input_l output_rows_2).
  {
    apply PreH22; assumption.
  }
  Exists output_ptrs_2 output_rows_2 out_size data_2.
  entailer!.
  rewrite PreH24.
  apply derivable1_refl.
Qed.
