Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Lia.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE Require Import p012_longest_goal.
From SimpleC.EE Require Import p012_longest_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p012_longest.
Local Open Scope sac.
Local Open Scope bool_scope.
Local Open Scope list_scope.

(* Helper lemmas moved from the contract file; keep input/annotated_input proof-free. *)

Lemma String_length_string_of_list_z_12 : forall l,
  String.length (string_of_list_z_12 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_string_length_z_12 : forall row,
  Z.of_nat (String.length (row_string_z_12 row)) = row_len_z_12 row.
Proof.
  intros row.
  unfold row_string_z_12, row_len_z_12, string_length.
  rewrite String_length_string_of_list_z_12.
  rewrite Zlength_correct.
  reflexivity.
Qed.

Lemma problem_12_spec_none_z_intro : forall rows,
  Zlength rows = 0 ->
  problem_12_spec_none_z rows.
Proof.
  intros rows Hlen.
  unfold problem_12_spec_none_z, rows_to_strings_z_12.
  left.
  split; [| reflexivity].
  apply Zlength_nil_inv in Hlen.
  subst; reflexivity.
Qed.

Lemma longest_prefix_z_12_initial : forall rows,
  longest_prefix_z_12 rows 0 (-1) (-1).
Proof.
  intros rows.
  unfold longest_prefix_z_12.
  split; [rewrite Zlength_correct; lia|].
  left; auto.
Qed.

Lemma longest_prefix_z_12_nonempty_bounds : forall rows k best_idx best_len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 < k ->
  0 <= best_idx < k.
Proof.
  intros rows k best_idx best_len Hpref Hk.
  unfold longest_prefix_z_12 in Hpref.
  destruct Hpref as [_ [[Hz _] | [_ [Hb _]]]]; lia.
Qed.

Lemma nth_error_Znth_12 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  nth_error l (Z.to_nat i) = Some (Znth i l d).
Proof.
  intros A l i d Hi.
  unfold Znth.
  apply nth_error_nth'.
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma longest_prefix_z_12_step_update : forall rows k best_idx best_len len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 <= k < Zlength rows ->
  len = row_len_z_12 (Znth k rows nil) ->
  best_len < len ->
  longest_prefix_z_12 rows (k + 1) k len.
Proof.
  intros rows k best_idx best_len len Hpref Hk Hlen Hgt.
  unfold longest_prefix_z_12 in *.
  destruct Hpref as [Hkbounds Hcase].
  split; [lia|].
  right.
  split; [lia|].
  split; [lia|].
  split; [assumption|].
  split.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + lia.
    + assert (0 <= j < k) by lia.
      destruct Hcase as [[Hz [Hbi Hbest]] | [_ [_ [_ [Hall _]]]]].
      * subst; lia.
      * specialize (Hall j ltac:(lia)); lia.
  - intros j Hj.
    destruct Hcase as [[Hz [Hbi Hbest]] | [_ [_ [_ [Hall _]]]]].
    + subst; lia.
    + specialize (Hall j ltac:(lia)); lia.
Qed.

Lemma longest_prefix_z_12_step_keep : forall rows k best_idx best_len len,
  longest_prefix_z_12 rows k best_idx best_len ->
  0 <= k < Zlength rows ->
  len = row_len_z_12 (Znth k rows nil) ->
  len <= best_len ->
  longest_prefix_z_12 rows (k + 1) best_idx best_len.
Proof.
  intros rows k best_idx best_len len Hpref Hk Hlen Hle.
  unfold longest_prefix_z_12 in *.
  destruct Hpref as [Hkbounds Hcase].
  destruct Hcase as [[Hz [Hbi Hbest]] | [Hkpos [Hb [Hbest [Hall Hfirst]]]]].
  - pose proof (string_length_nonneg (row_payload_z_12 (Znth k rows nil))) as Hnonneg.
    unfold row_len_z_12 in Hlen.
    lia.
  - split; [lia|].
    right.
    split; [lia|].
    split; [lia|].
    split; [assumption|].
    split.
    + intros j Hj.
      destruct (Z.eq_dec j k) as [-> | Hne].
      * lia.
      * apply Hall; lia.
    + intros j Hj.
      apply Hfirst; lia.
Qed.

Lemma longest_prefix_z_12_final_spec : forall rows best_idx best_len,
  rows_well_formed_12 rows (Zlength rows) ->
  problem_12_pre_z rows ->
  0 < Zlength rows ->
  longest_prefix_z_12 rows (Zlength rows) best_idx best_len ->
  problem_12_spec_some_z rows best_idx.
Proof.
  intros rows best_idx best_len _ _ Hnonempty Hpref.
  unfold problem_12_spec_some_z, problem_12_spec.
  right.
  exists (row_string_z_12 (Znth best_idx rows nil)), (Z.to_nat best_idx).
  unfold rows_to_strings_z_12.
  unfold longest_prefix_z_12 in Hpref.
  destruct Hpref as [_ [[Hz _] | [_ [Hb [Hbest [Hall Hfirst]]]]]]; [lia|].
  repeat split; auto.
  - apply Nat2Z.inj_lt.
    rewrite Nat2Z.inj_0, length_map.
    rewrite <- Zlength_correct.
    lia.
  - rewrite length_map.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
  - rewrite nth_error_map.
    rewrite (nth_error_Znth_12 rows best_idx nil) by lia.
    reflexivity.
  - intros j Hj.
    exists (row_string_z_12 (Znth (Z.of_nat j) rows nil)).
    intros _.
    apply Nat2Z.inj_le.
    rewrite !row_string_length_z_12.
    rewrite <- Hbest.
    apply Hall.
    split; [lia|].
    apply Nat2Z.inj_lt in Hj.
    rewrite length_map in Hj.
    rewrite <- Zlength_correct in Hj.
    lia.
  - intros j Hj.
    exists (row_string_z_12 (Znth (Z.of_nat j) rows nil)).
    intros _.
    apply Nat2Z.inj_lt.
    rewrite !row_string_length_z_12.
    rewrite <- Hbest.
    apply Hfirst.
    split; [lia|].
    apply Nat2Z.inj_lt in Hj.
    rewrite Z2Nat.id in Hj by lia.
    lia.
Qed.

Lemma rows_well_formed_12_row : forall rows n k,
  rows_well_formed_12 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_12 row in
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
  change (Zlength (Znth k rows nil) =
          Zlength (row_payload_z_12 (Znth k rows nil)) + 1).
  rewrite Hrow at 1.
  unfold c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Local Close Scope bool_scope.

Lemma proof_of_longest_entail_wit_1 : longest_entail_wit_1.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  apply longest_prefix_z_12_initial.
Qed.

Lemma proof_of_longest_entail_wit_2 : longest_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i strings_pre i strings_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)).
    entailer!.
Qed.

Lemma proof_of_longest_entail_wit_3 : longest_entail_wit_3.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  all: match goal with
  | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
      pose proof (rows_well_formed_12_row rs n i Hwf ltac:(lia))
        as [Hrow [Hvalid [Hlt Hlen]]]
  end.
  all: try solve [
    unfold store_string;
    rewrite <- Hlen;
    rewrite <- Hrow;
    entailer!
  ].
  all: try solve [exact Hlen | exact Hlt | exact Hvalid].
Qed.

Lemma proof_of_longest_entail_wit_4 : longest_entail_wit_4.
Proof.
  pre_process_default; try entailer!; try cancel; try lia.
  all: match goal with
  | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
      pose proof (rows_well_formed_12_row rs n i Hwf ltac:(lia))
        as [Hrow [Hvalid [Hlt Hlen]]]
  end.
  all: try solve [
    unfold row_len_z_12;
    pose proof (string_length_nonneg (row_payload_z_12 (Znth i rows nil)));
    lia
  ].
  all: try solve [
    unfold store_string;
    rewrite <- Hlen;
    rewrite <- Hrow;
    entailer!
  ].
Qed.

Lemma proof_of_longest_entail_wit_5_1 : longest_entail_wit_5_1.
Proof.
  pre_process_default; try entailer!; try lia.
  all: try solve [
    match goal with
    | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
        destruct Hwf as [Hrows_len Hrows_wf];
        eapply longest_prefix_z_12_step_keep; eauto; try (rewrite Hrows_len; lia); lia
    end
  ].
  all: try solve [
    pose proof (CharPtrArray2.missing_i_merge_to_full
        strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr in Hmerge;
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge;
    try rewrite sizeof_ptr;
    sep_apply Hmerge; try lia;
    rewrite replace_Znth_Znth by lia;
    entailer!
  ].
Qed.

Lemma proof_of_longest_entail_wit_5_2 : longest_entail_wit_5_2.
Proof.
  pre_process_default; try entailer!; try lia.
  all: try solve [
    match goal with
    | Hwf : rows_well_formed_12 ?rs ?n |- _ =>
        destruct Hwf as [Hrows_len Hrows_wf];
        eapply longest_prefix_z_12_step_update; eauto; try (rewrite Hrows_len; lia); lia
    end
  ].
  all: try solve [
    pose proof (CharPtrArray2.missing_i_merge_to_full
        strings_pre i strings_size_pre row_ptr rows (Znth i rows nil)) as Hmerge;
    unfold StorePtrAsElement.storeA in Hmerge;
    try rewrite sizeof_ptr in Hmerge;
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge;
    try rewrite sizeof_ptr;
    sep_apply Hmerge; try lia;
    rewrite replace_Znth_Znth by lia;
    entailer!
  ].
Qed.

Lemma proof_of_longest_entail_wit_7 : longest_entail_wit_7.
Proof.
  pre_process_default.
  assert (Hi_eq : i = strings_size_pre) by lia.
  subst i.
  pose proof PreH8 as Hwf_all.
  destruct PreH8 as [Hrows_len Hrows_wf].
  pose proof (longest_prefix_z_12_nonempty_bounds rows strings_size_pre best_idx best PreH10 ltac:(lia)) as Hbest_bounds.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i strings_pre best_idx strings_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil))
      with (CharArray.full row_ptr (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil)).
    entailer!.
    eapply longest_prefix_z_12_final_spec with (best_len := best); eauto; try lia;
      try (rewrite Hrows_len; exact Hwf_all);
      try (rewrite Hrows_len; exact PreH10).
Qed.

Lemma proof_of_longest_return_wit_2 : longest_return_wit_2.
Proof.
  pre_process_default.
  eapply derivable1_trans with
    (y := “ strings_size_pre = 0 ” &&
          (“ 0 = 0 ” &&
           (“ problem_12_spec_none_z rows ” &&
            CharPtrArray2.full strings_pre strings_size_pre rows))).
  - entailer!.
    eapply problem_12_spec_none_z_intro.
    destruct PreH4 as [Hlen _].
    lia.
  - apply derivable1_orp_intros1.
Qed.
