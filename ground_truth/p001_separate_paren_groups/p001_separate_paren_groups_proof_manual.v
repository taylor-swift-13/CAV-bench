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
From SimpleC.EE.CAV.ground_truth_p001_separate_paren_groups Require Import p001_separate_paren_groups_goal.
From SimpleC.EE.CAV.ground_truth_p001_separate_paren_groups Require Import p001_separate_paren_groups_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p001_separate_paren_groups.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope string_scope.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.



Lemma paren_rows_heap_1_nil :
  emp |-- paren_rows_heap_1 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma paren_rows_heap_1_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  paren_rows_heap_1 ptrs rows ** CharArray.full p (Zlength row) row
  |-- paren_rows_heap_1 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows).
    lia.
  - rewrite Zlength_nil in Hlen.
    rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs).
    lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma String_length_string_of_list_z_1 : forall l,
  String.length (string_of_list_z_1 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_payload_c_string_1 : forall payload,
  row_payload_z_1 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_1, c_string.
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

Lemma rows_to_strings_c_string_1 : forall payloads,
  rows_to_strings_z_1 (map c_string payloads) =
  map string_of_list_z_1 payloads.
Proof.
  induction payloads as [| p ps IH]; simpl; [reflexivity|].
  unfold row_string_z_1.
  rewrite row_payload_c_string_1.
  rewrite IH.
  reflexivity.
Qed.

Lemma Zlength_map_1 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma Zlength_paren_payload_1 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (paren_payload_1 s start stop) = stop - start.
Proof.
  intros s start stop Hlo Hhi.
  unfold paren_payload_1.
  rewrite Zlength_sublist; lia.
Qed.

Lemma paren_payload_c_string_1 : forall s start stop,
  0 <= start <= stop ->
  stop <= string_length s ->
  sublist start stop (c_string s) = paren_payload_1 s start stop.
Proof.
  intros s start stop Hlo Hhi.
  unfold paren_payload_1, c_string, string_length in *.
  apply sublist_split_app_l; lia.
Qed.

Lemma paren_scan_state_1_initial : forall s,
  paren_scan_state_1 s 0 0 (-1) [].
Proof.
  intros s.
  unfold paren_scan_state_1, paren_completed_rows_1,
    paren_scan_level_1, paren_scan_start_1, string_length.
  simpl.
  repeat split; try rewrite Zlength_correct; try lia; auto.
Qed.

Lemma paren_state_nat_1_step : forall i s,
  0 <= i ->
  paren_state_nat_1 (Z.to_nat (i + 1)) s =
  paren_step_1 s (paren_state_nat_1 (Z.to_nat i) s) i (Znth i s 0).
Proof.
  intros i s Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma c_string_Znth_before_1 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma paren_payload_1_empty : forall s start,
  paren_payload_1 s start start = [].
Proof.
  intros s start.
  unfold paren_payload_1.
  apply sublist_nil.
  lia.
Qed.

Lemma paren_payload_1_step : forall s start i,
  0 <= start <= i ->
  i < Zlength s ->
  paren_payload_1 s start (i + 1) =
  paren_payload_1 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds Hi.
  unfold paren_payload_1.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry; apply sublist_single; lia.
Qed.

Lemma paren_payload_1_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  paren_payload_1 s start (start + (k + 1)) =
  paren_payload_1 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite paren_payload_1_step by lia.
  rewrite c_string_Znth_before_1 by lia.
  reflexivity.
Qed.

Lemma paren_row_1_unfold : forall s start stop,
  paren_row_1 s start stop = paren_payload_1 s start stop ++ [0].
Proof.
  intros.
  unfold paren_row_1, c_string.
  reflexivity.
Qed.

Lemma paren_scan_state_1_change_level : forall s i level level' start rows,
  paren_scan_state_1 s i level start rows ->
  level = level' ->
  paren_scan_state_1 s i level' start rows.
Proof.
  intros; subst; auto.
Qed.

Lemma paren_scan_state_1_step_open_continue : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  level <> 0 ->
  Znth i (c_string s) 0 = 40 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) (level + 1) start rows.
Proof.
  intros s i level start rows Hstate Hlevel Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    assert (Hlevel0 : level0 <> 0).
    { intro Hz; apply Hlevel; rewrite Hlev; exact Hz. }
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    assert (Hlevel0 : level0 <> 0).
    { intro Hz; apply Hlevel; lia. }
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    assert (Hlevel0 : level0 <> 0).
    {
      intro Hz.
      apply Hlevel.
      rewrite Hlev.
      unfold paren_scan_level_1.
      rewrite Hst.
      simpl.
      exact Hz.
    }
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec level0 0) as [Heq | Hneq].
    + subst level0; contradiction.
    + reflexivity.
Qed.

Lemma paren_scan_state_1_step_open_start : forall s i rows,
  paren_scan_state_1 s i 0 (-1) rows ->
  Znth i (c_string s) 0 = 40 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) 1 i rows.
Proof.
  intros s i rows Hstate Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst rows.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite <- Hlev.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    rewrite <- Hlev.
    rewrite Z.eqb_refl.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_space : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  Znth i (c_string s) 0 = 32 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) level start rows.
Proof.
  intros s i level start rows Hstate Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
  - unfold paren_scan_level_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_close_finish : forall s i start rows,
  paren_scan_state_1 s i 1 start rows ->
  0 <= start <= i ->
  Znth i (c_string s) 0 = 41 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) 0 (-1)
    (rows ++ [paren_row_1 s start (i + 1)]).
Proof.
  intros s i start rows Hstate Hstart_bounds Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst rows start0.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    unfold paren_row_1, paren_payload_1.
    reflexivity.
  - unfold paren_scan_level_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
  - unfold paren_scan_start_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    replace (level0 - 1) with 0 by lia.
    rewrite Z.eqb_refl.
    reflexivity.
Qed.

Lemma paren_scan_state_1_step_close_continue : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  paren_safe_input_1 s ->
  level - 1 <> 0 ->
  Znth i (c_string s) 0 = 41 ->
  i < Zlength s ->
  paren_scan_state_1 s (i + 1) (level - 1) start rows.
Proof.
  intros s i level start rows Hstate Hsafe Hlevel Hch Hi.
  unfold paren_scan_state_1 in *.
  destruct Hstate as [Hbounds [Hrows [Hlev [Hstart [Hnonneg Hcases]]]]].
  assert (Hpos : 0 < level).
  {
    unfold paren_safe_input_1 in Hsafe.
    destruct Hsafe as [Hsafe _].
    specialize (Hsafe i ltac:(unfold string_length in *; lia) Hch).
    unfold paren_scan_state_1 in *.
    lia.
  }
  repeat split; try (unfold string_length in *; lia).
  - unfold paren_completed_rows_1 in *.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst rows level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
  - unfold paren_scan_level_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    subst level.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
  - unfold paren_scan_start_1.
    rewrite paren_state_nat_1_step by lia.
    destruct (paren_state_nat_1 (Z.to_nat i) s) as [[rows0 level0] start0] eqn:Hst.
    simpl in *.
    unfold paren_scan_level_1 in Hlev; rewrite Hst in Hlev; simpl in Hlev.
    unfold paren_scan_start_1 in Hstart; rewrite Hst in Hstart; simpl in Hstart.
    subst level start.
    unfold paren_step_1.
    rewrite <- (c_string_Znth_before_1 s i) by lia.
    rewrite Hch.
    destruct (Z.eqb_spec (level0 - 1) 0) as [Heq | Hneq].
    + contradiction.
    + reflexivity.
Qed.

Lemma valid_paren_input_1_space : forall s i,
  valid_paren_input_1 s ->
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 <> 41 ->
  Znth i (c_string s) 0 <> 40 ->
  Znth i (c_string s) 0 = 32.
Proof.
  intros s i Hvalid Hi Hnot_close Hnot_open.
  rewrite c_string_Znth_before_1 by lia.
  unfold valid_paren_input_1, valid_paren_char_1 in Hvalid.
  specialize (Hvalid i Hi).
  rewrite c_string_Znth_before_1 in Hnot_close by lia.
  rewrite c_string_Znth_before_1 in Hnot_open by lia.
  destruct Hvalid as [Hspace | [Hopen | Hclose]]; congruence.
Qed.

Lemma paren_scan_state_1_level0_start : forall s i start rows,
  paren_scan_state_1 s i 0 start rows ->
  start = -1.
Proof.
  intros s i start rows Hstate.
  unfold paren_scan_state_1 in Hstate.
  destruct Hstate as [_ [_ [_ [_ [_ Hcases]]]]].
  destruct Hcases as [[_ Hstart] | [Hbad _]]; lia.
Qed.

Lemma paren_scan_state_1_nonzero_start : forall s i level start rows,
  paren_scan_state_1 s i level start rows ->
  level <> 0 ->
  0 <= start.
Proof.
  intros s i level start rows Hstate Hlevel.
  unfold paren_scan_state_1 in Hstate.
  destruct Hstate as [_ [_ [_ [_ [_ Hcases]]]]].
  destruct Hcases as [[Hzero _] | [_ [Hstart _]]]; lia.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_c_string_char_bound_1 :=
  match goal with
  | Hvalid : valid_string ?s |- 0 <= Znth ?i (c_string ?s) 0 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  | Hvalid : valid_string ?s |- Znth ?i (c_string ?s) 0 <= 127 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  end.

Ltac paren_entailer :=
  entailer!;
  try solve_c_string_char_bound_1;
  try lia.

Lemma proof_of_separate_paren_groups_entail_wit_1 : separate_paren_groups_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  subst retval.
  Exists (@nil Z) (@nil (list Z)).
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 (string_length str_l + 1)).
  rewrite PtrArray.seg_empty.
  change (paren_rows_heap_1 (@nil Z) (@nil (list Z))) with emp.
  unfold store_string.
  entailer!.
  - rewrite Zlength_nil.
    cancel.
  - apply paren_scan_state_1_initial.
  - apply string_length_nonneg.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_2_1 : separate_paren_groups_entail_wit_2_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - eapply paren_scan_state_1_step_open_continue; eauto.
    unfold string_length in *; lia.
  - eapply paren_scan_state_1_nonzero_start; eauto.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_2_2 : separate_paren_groups_entail_wit_2_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hstart0 : start = -1) by
    (eapply paren_scan_state_1_level0_start; rewrite <- PreH1; exact PreH27).
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - rewrite Hstart0 in PreH27.
    rewrite PreH1 in PreH27.
    replace (level + 1) with 1 by lia.
    eapply paren_scan_state_1_step_open_start; eauto.
    unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_3 : separate_paren_groups_entail_wit_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hlevel1 : level = 1) by lia.
  rewrite Hlevel1 in PreH30.
  pose proof (paren_scan_state_1_nonzero_start _ _ _ _ _ PreH30 ltac:(lia)) as Hstart_nonneg.
  replace (start + 0) with start by lia.
  rewrite paren_payload_1_empty.
  rewrite CharArray.full_empty.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval (((i - start) + 1) + 1)).
  unfold store_string.
  paren_entailer.
  - rewrite PreH14, PreH9.
    cancel.
  - rewrite Zlength_paren_payload_1; unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_4 : separate_paren_groups_entail_wit_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  rewrite <- paren_payload_1_step_offset_c_string by (unfold string_length in *; lia).
  unfold store_string.
  paren_entailer.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_5 : separate_paren_groups_entail_wit_5.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  replace k with len by lia.
  replace (start + len) with (i + 1) by lia.
  rewrite paren_row_1_unfold.
  rewrite CharArray.undef_seg_empty.
  unfold store_string.
  paren_entailer.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_6 : separate_paren_groups_entail_wit_6.
Proof.
  constructor; pre_process_default.
  Exists (app output_ptrs_2 (cons row nil))
    (app output_rows_2 (cons (paren_row_1 str_l start (i + 1)) nil)).
  assert (Hpayload_len : Zlength (paren_payload_1 str_l start (i + 1)) = len) by
    (rewrite Zlength_paren_payload_1 by (unfold string_length in *; lia); lia).
  assert (Hrow_len : Zlength (paren_row_1 str_l start (i + 1)) = len + 1) by
    (rewrite paren_row_1_unfold, Zlength_app, Hpayload_len,
       Zlength_cons, Zlength_nil; lia).
  replace (len + 1) with (Zlength (paren_row_1 str_l start (i + 1))) by lia.
  sep_apply (paren_rows_heap_1_app_single output_ptrs_2 output_rows_2 row
    (paren_row_1 str_l start (i + 1)) ltac:(lia)).
  rewrite PreH15.
  unfold store_string.
  paren_entailer.
  - eapply paren_scan_state_1_step_close_finish.
    + exact PreH25.
    + lia.
    + unfold naive_C_Rules.c_string, c_string in *; lia.
    + unfold string_length in *; lia.
  - rewrite Zlength_app, PreH12.
    rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, PreH11.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_7 : separate_paren_groups_entail_wit_7.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hlevel_pos : 0 < level).
  {
    unfold paren_safe_input_1 in PreH25.
    destruct PreH25 as [PreH25 _].
    specialize (PreH25 i ltac:(unfold string_length in *; lia) PreH2).
    unfold paren_scan_state_1 in PreH28.
    lia.
  }
  unfold store_string.
  paren_entailer.
  - rewrite PreH12, PreH7.
    cancel.
  - eapply paren_scan_state_1_step_close_continue; eauto.
    unfold string_length in *; lia.
  - eapply paren_scan_state_1_nonzero_start; eauto.
    intro Hzero; subst level.
    unfold paren_safe_input_1 in PreH25.
    destruct PreH25 as [PreH25 _].
    specialize (PreH25 i ltac:(unfold string_length in *; lia) PreH2).
    unfold paren_scan_state_1 in PreH28.
    lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_8 : separate_paren_groups_entail_wit_8.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  pose proof (valid_paren_input_1_space str_l i PreH23
    ltac:(unfold string_length in *; lia) PreH1 PreH2) as Hspace.
  unfold store_string.
  paren_entailer.
  - rewrite PreH11, PreH6.
    cancel.
  - eapply paren_scan_state_1_step_space; eauto.
    unfold string_length in *; lia.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_1 : separate_paren_groups_entail_wit_9_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_2 : separate_paren_groups_entail_wit_9_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH9, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_3 : separate_paren_groups_entail_wit_9_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_9_4 : separate_paren_groups_entail_wit_9_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  paren_entailer.
  - rewrite PreH8, PreH3.
    cancel.
Qed.

Lemma proof_of_separate_paren_groups_entail_wit_10 : separate_paren_groups_entail_wit_10.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  assert (Hi_done : i = Zlength str_l) by (unfold string_length in *; lia).
  pose proof PreH22 as Hsafe_all.
  unfold paren_safe_input_1 in PreH22.
  destruct PreH22 as [_ [Hlevel_done [Hstart_done Hspec]]].
  assert (Hrows_done : output_rows_2 = paren_output_rows_1 str_l).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [Hrows _]].
    unfold paren_output_rows_1.
    rewrite Hrows, Hi_done.
    reflexivity.
  }
  assert (Hlevel0 : level = 0).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [_ [Hlev _]]].
    rewrite Hlev, Hi_done.
    exact Hlevel_done.
  }
  assert (Hstart0 : start = -1).
  {
    unfold paren_scan_state_1 in PreH25.
    destruct PreH25 as [_ [_ [_ [Hstart _]]]].
    rewrite Hstart, Hi_done.
    exact Hstart_done.
  }
  unfold store_string.
  paren_entailer.
  - rewrite Hrows_done.
    exact Hspec.
Qed.
