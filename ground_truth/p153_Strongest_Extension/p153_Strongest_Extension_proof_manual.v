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
From SimpleC.EE.CAV.ground_truth_p153_Strongest_Extension Require Import p153_Strongest_Extension_goal.
From SimpleC.EE.CAV.ground_truth_p153_Strongest_Extension Require Import p153_Strongest_Extension_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p153_Strongest_Extension.
Local Open Scope sac.

Ltac rewrite_delta_153 :=
  repeat match goal with
  | H : ?c < 65 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_low c H)
  | H1 : 90 < ?c, H2 : ?c < 97 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_mid c (conj H1 H2))
  | H1 : ?c > 90, H2 : ?c < 97 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_mid c (conj H1 H2))
  | H1 : 65 <= ?c, H2 : ?c <= 90 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_upper c (conj H1 H2))
  | H1 : ?c >= 65, H2 : ?c <= 90 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_upper c (conj H1 H2))
  | H1 : 97 <= ?c, H2 : ?c <= 122 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_lower c (conj H1 H2))
  | H1 : ?c >= 97, H2 : ?c <= 122 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_lower c (conj H1 H2))
  | H : 122 < ?c |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_high c H)
  | H : ?c > 122 |- context[char_strength_delta_153 ?c] =>
      rewrite (char_strength_delta_153_high c H)
  end.

Ltac solve_strength_scan_153 :=
  match goal with
  | |- strength_scan_state_153 _ 0 0 =>
      apply strength_scan_state_153_initial
  | Hstate : strength_scan_state_153 ?s ?j ?strength,
    Hchr : ?chr = Znth ?j ?s 0 |- strength_scan_state_153 ?s (?j + 1) ?new_strength =>
      eapply strength_scan_state_153_step_eq;
      [lia | exact Hchr | exact Hstate | rewrite_delta_153; lia]
  | Hstate : strength_scan_state_153 ?s ?j ?strength
    |- ?strength = extension_strength_z ?s =>
      eapply strength_scan_state_153_finish; [lia | exact Hstate]
  end.

Ltac solve_best_prefix_153 :=
  match goal with
  | Hwf : rows_well_formed_153 ?rows ?n |- best_prefix_state_153 ?rows 1 0 _ =>
      apply best_prefix_state_153_initial with (n := n); [exact Hwf | lia]
  | Hstate : best_prefix_state_153 ?rows ?i ?best ?max,
    Hcur : ?strength = extension_strength_z (row_payload_z_153 (Znth ?i ?rows nil)),
    Hcmp : ?strength <= ?max
    |- best_prefix_state_153 ?rows (?i + 1) ?best ?max =>
      eapply best_prefix_state_153_step_keep; eauto; lia
  | Hstate : best_prefix_state_153 ?rows ?i ?best ?max,
    Hcur : ?strength = extension_strength_z (row_payload_z_153 (Znth ?i ?rows nil)),
    Hcmp : ?max < ?strength
    |- best_prefix_state_153 ?rows (?i + 1) ?i ?strength =>
      eapply best_prefix_state_153_step_update; eauto; lia
  end.

Ltac solve_problem_spec_153 :=
  match goal with
  | Hwf : rows_well_formed_153 ?rows ?n,
    Hpre : problem_153_pre_z ?class_l ?rows,
    Hbest : best_prefix_state_153 ?rows ?n ?best ?max
    |- problem_153_spec_z ?class_l ?rows
         (output_payload_153 ?class_l (row_payload_z_153 (Znth ?best ?rows nil))) =>
      eapply best_prefix_state_153_problem_spec; eauto
  end.

Ltac destruct_strength_states_153 :=
  repeat match goal with
  | H : strength_scan_state_153 _ _ _ |- _ =>
      let Hb := fresh "Hscan_bounds" in
      let Heq := fresh "Hscan_eq" in
      let Hr := fresh "Hscan_range" in
      unfold strength_scan_state_153 in H;
      destruct H as [Hb [Heq Hr]]
  end.

Ltac destruct_valid_strings_153 :=
  repeat match goal with
  | H : string_lib.valid_string _ |- _ =>
      let Hall := fresh "Hall_ascii" in
      let Hnul := fresh "Hno_nul" in
      unfold string_lib.valid_string in H;
      destruct H as [Hall Hnul]
  end.

Ltac solve_153 :=
  pre_process; simpl in *; entailer!;
  try solve [
    left; solve_153
  | right; solve_153
  | solve_strength_scan_153
  | solve_best_prefix_153
  | solve_problem_spec_153
  | eapply rows_well_formed_153_row; eauto; lia
  | unfold row_len_z_153; lia
  | match goal with
    | Hsafe : output_len_safe_153 ?class_l ?rows ?n,
      Hidx1 : 0 <= ?idx,
      Hidx2 : ?idx < ?n,
      Hn1 : ?n1 = string_lib.string_length ?class_l,
      Hn2 : ?n2 = row_len_z_153 (Znth ?idx ?rows nil)
      |- _ =>
        specialize (Hsafe idx ltac:(lia));
        unfold row_len_z_153 in *; lia
    end
  | destruct_strength_states_153; lia
  | apply string_lib.string_length_nonneg
  | match goal with
    | H : ?retval = string_lib.string_length ?str |- 0 <= ?retval =>
        rewrite H; apply string_lib.string_length_nonneg
    | H : ?n1 = string_lib.string_length ?str |- INT_MIN <= ?n1 + 1 =>
        rewrite H; pose proof (string_lib.string_length_nonneg str); lia
    | Hn1 : ?n1 = string_lib.string_length ?class_l,
      Hn2 : ?n2 = row_len_z_153 (Znth ?idx ?rows nil)
      |- INT_MIN <= (?n1 + ?n2) + 1 =>
        rewrite Hn1; unfold row_len_z_153 in Hn2; rewrite Hn2;
        pose proof (string_lib.string_length_nonneg class_l);
        pose proof (string_lib.string_length_nonneg (row_payload_z_153 (Znth idx rows nil)));
        lia
    | Hn1 : ?n1 = string_lib.string_length ?class_l,
      Hn2 : ?n2 = row_len_z_153 (Znth ?idx ?rows nil)
      |- INT_MIN <= ?n1 + ?n2 =>
        rewrite Hn1; unfold row_len_z_153 in Hn2; rewrite Hn2;
        pose proof (string_lib.string_length_nonneg class_l);
        pose proof (string_lib.string_length_nonneg (row_payload_z_153 (Znth idx rows nil)));
        lia
    end
  | rewrite string_lib.c_string_Znth_inside by lia; reflexivity
  | match goal with
    | H : string_lib.valid_string _ |- _ =>
        destruct H as [Hall_ascii _];
        rewrite c_string_Znth_inside by lia;
        pose proof (Hall_ascii _ ltac:(lia)); lia
    end
  | destruct_valid_strings_153;
    match goal with
    | H : string_lib.all_ascii ?str |- 0 <= Znth ?j (string_lib.c_string ?str) 0 =>
        rewrite string_lib.c_string_Znth_inside by lia; apply H; lia
    | H : string_lib.all_ascii ?str |- Znth ?j (string_lib.c_string ?str) 0 <= 127 =>
        rewrite string_lib.c_string_Znth_inside by lia; apply H; lia
    | H : string_lib.all_ascii ?str |- 0 <= Znth ?j ?str 0 =>
        apply H; lia
    | H : string_lib.all_ascii ?str |- Znth ?j ?str 0 <= 127 =>
        apply H; lia
    end
  | rewrite output_payload_string_153; reflexivity
  | lia
  | cancel
  ].

Lemma proof_of_extension_strength_safety_wit_6_split_goal_1 : extension_strength_safety_wit_6_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_safety_wit_6_split_goal_2 : extension_strength_safety_wit_6_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_safety_wit_6 : extension_strength_safety_wit_6.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_safety_wit_14_split_goal_1 : extension_strength_safety_wit_14_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_safety_wit_14_split_goal_2 : extension_strength_safety_wit_14_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_safety_wit_14 : extension_strength_safety_wit_14.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_1_split_goal_1 : extension_strength_entail_wit_1_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_1_split_goal_2 : extension_strength_entail_wit_1_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_1 : extension_strength_entail_wit_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_2_split_goal_1 : extension_strength_entail_wit_2_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_2_split_goal_2 : extension_strength_entail_wit_2_split_goal_2.
Proof.
  pre_process; simpl in *; entailer!;
  destruct PreH7 as [Hall_ascii _].
  assert (Hj_in : 0 <= j < string_length str) by lia.
  rewrite (c_string_Znth_inside str j 0 Hj_in).
  unfold string_length in Hj_in.
  pose proof (Hall_ascii j Hj_in).
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_2_split_goal_3 : extension_strength_entail_wit_2_split_goal_3.
Proof.
  pre_process; simpl in *; entailer!;
  destruct PreH7 as [Hall_ascii _].
  assert (Hj_in : 0 <= j < string_length str) by lia.
  rewrite (c_string_Znth_inside str j 0 Hj_in).
  unfold string_length in Hj_in.
  pose proof (Hall_ascii j Hj_in).
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_2 : extension_strength_entail_wit_2.
Proof.
  right.
  pre_process; simpl in *; entailer!.
  all: try solve_153.
  all: destruct PreH7 as [Hall_ascii _];
       assert (Hj_in : 0 <= j < string_length str) by lia;
       rewrite (c_string_Znth_inside str j 0 Hj_in);
       unfold string_length in Hj_in;
       pose proof (Hall_ascii j Hj_in);
       lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_1_split_goal_1 : extension_strength_entail_wit_3_1_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_3_1 : extension_strength_entail_wit_3_1.
Proof. solve_153. Qed.
Lemma proof_of_extension_strength_entail_wit_3_2_split_goal_1 : extension_strength_entail_wit_3_2_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_mid chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_2 : extension_strength_entail_wit_3_2.
Proof.
  right.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_mid chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_3_split_goal_1 : extension_strength_entail_wit_3_3_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_upper chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_3 : extension_strength_entail_wit_3_3.
Proof.
  right.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_upper chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_4_split_goal_1 : extension_strength_entail_wit_3_4_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_high chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_4 : extension_strength_entail_wit_3_4.
Proof.
  right.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_high chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_5_split_goal_1 : extension_strength_entail_wit_3_5_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_lower chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_entail_wit_3_5 : extension_strength_entail_wit_3_5.
Proof.
  right.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_step_eq with (c := chr); eauto; try lia.
  rewrite (char_strength_delta_153_lower chr) by lia.
  lia.
Qed.
Lemma proof_of_extension_strength_return_wit_1_split_goal_1 : extension_strength_return_wit_1_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_finish; eauto; lia.
Qed.
Lemma proof_of_extension_strength_return_wit_1 : extension_strength_return_wit_1.
Proof.
  left.
  pre_process; simpl in *; entailer!.
  eapply strength_scan_state_153_finish; eauto; lia.
Qed.
Lemma proof_of_Strongest_Extension_safety_wit_18_split_goal_1 : Strongest_Extension_safety_wit_18_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_18_split_goal_2 : Strongest_Extension_safety_wit_18_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_18 : Strongest_Extension_safety_wit_18.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_20_split_goal_1 : Strongest_Extension_safety_wit_20_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_20_split_goal_2 : Strongest_Extension_safety_wit_20_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_20 : Strongest_Extension_safety_wit_20.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_21_split_goal_1 : Strongest_Extension_safety_wit_21_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_21_split_goal_2 : Strongest_Extension_safety_wit_21_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_safety_wit_21 : Strongest_Extension_safety_wit_21.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_1_split_goal_1 : Strongest_Extension_entail_wit_1_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH7 ltac:(lia))
    as [_ [_ [_ [Hlt _]]]].
  exact Hlt.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_1_split_goal_2 : Strongest_Extension_entail_wit_1_split_goal_2.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH7 ltac:(lia))
    as [_ [_ [Hle _]]].
  exact Hle.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_1_split_goal_3 : Strongest_Extension_entail_wit_1_split_goal_3.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH7 ltac:(lia))
    as [_ [Hvalid _]].
  exact Hvalid.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_1_split_goal_spatial : Strongest_Extension_entail_wit_1_split_goal_spatial.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH7 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx0 : 0 <= 0 < Zlength rows) by (destruct PreH7 as [Hlen _]; lia).
  rewrite (Znth_indep rows 0 __default__List_Z nil) by exact Hidx0.
  rewrite Hrow_len.
  rewrite Hrow_eq.
  rewrite row_payload_c_string_153.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_1 : Strongest_Extension_entail_wit_1.
Proof.
  left.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH5 ltac:(lia))
    as [Hrow_eq [Hvalid0 [Hlen_le0 [Hlen_lt0 Hrow_len0]]]].
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    extensions_pre 0 extensions_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth 0 rows nil)) (Znth 0 rows nil))
      with (CharArray.full row_ptr
        (Zlength (Znth 0 rows nil)) (Znth 0 rows nil)).
    rewrite Hrow_len0.
    rewrite Hrow_eq.
    rewrite row_payload_c_string_153.
    unfold store_string.
    entailer!.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_3_split_goal_spatial : Strongest_Extension_entail_wit_3_split_goal_spatial.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH13 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx0 : 0 <= 0 < extensions_size_pre) by (destruct PreH13 as [Hlen _]; lia).
  pose proof (CharPtrArray2.missing_i_merge_to_full
    extensions_pre 0 extensions_size_pre row_ptr rows (Znth 0 rows nil) Hidx0) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth 0 rows nil)) (Znth 0 rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth 0 rows nil)) (Znth 0 rows nil)) in Hmerge.
  rewrite Hrow_len in Hmerge.
  rewrite Hrow_eq in Hmerge.
  rewrite row_payload_c_string_153 in Hmerge.
  unfold store_string.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sepcon_lift (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows).
  sepcon_lift (CharArray.full row_ptr
    (string_length (row_payload_z_153 (Znth 0 rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth 0 rows nil)))).
  sepcon_lift (((extensions_pre + 0 * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_3 : Strongest_Extension_entail_wit_3.
Proof.
  right.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre 0 PreH13 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx0 : 0 <= 0 < extensions_size_pre) by (destruct PreH13 as [Hlen _]; lia).
  pose proof (CharPtrArray2.missing_i_merge_to_full
    extensions_pre 0 extensions_size_pre row_ptr rows (Znth 0 rows nil) Hidx0) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth 0 rows nil)) (Znth 0 rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth 0 rows nil)) (Znth 0 rows nil)) in Hmerge.
  rewrite Hrow_len in Hmerge.
  rewrite Hrow_eq in Hmerge.
  rewrite row_payload_c_string_153 in Hmerge.
  unfold store_string.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sepcon_lift (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows).
  sepcon_lift (CharArray.full row_ptr
    (string_length (row_payload_z_153 (Znth 0 rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth 0 rows nil)))).
  sepcon_lift (((extensions_pre + 0 * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_4_split_goal_1 : Strongest_Extension_entail_wit_4_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  subst.
  eapply best_prefix_state_153_initial; eauto; lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_4 : Strongest_Extension_entail_wit_4.
Proof.
  left.
  pre_process; simpl in *; entailer!.
  all: try solve [cancel | subst; eapply best_prefix_state_153_initial; eauto; lia].
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_5_split_goal_1 : Strongest_Extension_entail_wit_5_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_5_split_goal_2 : Strongest_Extension_entail_wit_5_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_5_split_goal_3 : Strongest_Extension_entail_wit_5_split_goal_3.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_5_split_goal_spatial : Strongest_Extension_entail_wit_5_split_goal_spatial.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre i PreH12 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx : 0 <= i < Zlength rows) by (destruct PreH12 as [Hlen _]; lia).
  rewrite (Znth_indep rows i __default__List_Z nil) by exact Hidx.
  rewrite Hrow_len.
  rewrite Hrow_eq.
  rewrite row_payload_c_string_153.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_5 : Strongest_Extension_entail_wit_5.
Proof.
  left.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre i PreH10 ltac:(lia))
    as [Hrow_eq [Hvalid [Hlen_le [Hlen_lt Hrow_len]]]].
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    extensions_pre i extensions_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil))
      with (CharArray.full row_ptr
        (Zlength (Znth i rows nil)) (Znth i rows nil)).
    rewrite Hrow_len.
    rewrite Hrow_eq.
    rewrite row_payload_c_string_153.
    unfold store_string.
    entailer!.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_7_split_goal_spatial : Strongest_Extension_entail_wit_7_split_goal_spatial.
Proof.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre i PreH12 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx : 0 <= i < extensions_size_pre) by lia.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    extensions_pre i extensions_size_pre row_ptr rows (Znth i rows nil) Hidx) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  rewrite Hrow_len in Hmerge.
  rewrite Hrow_eq in Hmerge.
  rewrite row_payload_c_string_153 in Hmerge.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sepcon_lift (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows).
  sepcon_lift (CharArray.full row_ptr
    (string_length (row_payload_z_153 (Znth i rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth i rows nil)))).
  sepcon_lift (((extensions_pre + i * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_7 : Strongest_Extension_entail_wit_7.
Proof.
  right.
  pre_process_default.
  pose proof (rows_well_formed_153_row rows extensions_size_pre i PreH12 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx : 0 <= i < extensions_size_pre) by lia.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    extensions_pre i extensions_size_pre row_ptr rows (Znth i rows nil) Hidx) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows nil)) (Znth i rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth i rows nil)) (Znth i rows nil)) in Hmerge.
  rewrite Hrow_len in Hmerge.
  rewrite Hrow_eq in Hmerge.
  rewrite row_payload_c_string_153 in Hmerge.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sepcon_lift (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows).
  sepcon_lift (CharArray.full row_ptr
    (string_length (row_payload_z_153 (Znth i rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth i rows nil)))).
  sepcon_lift (((extensions_pre + i * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_8_1_split_goal_1 : Strongest_Extension_entail_wit_8_1_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply best_prefix_state_153_step_keep with (cur_strength := strength).
  - exact PreH15.
  - destruct PreH12 as [Hlen _]; lia.
  - exact PreH7.
  - exact PreH2.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_8_1 : Strongest_Extension_entail_wit_8_1.
Proof.
  left.
  pre_process; simpl in *; entailer!.
  all: try solve [
    cancel
  | eapply best_prefix_state_153_step_keep with (cur_strength := strength);
    [exact PreH14 | destruct PreH11 as [Hlen _]; lia | exact PreH6 | exact PreH1]
  ].
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_8_2_split_goal_1 : Strongest_Extension_entail_wit_8_2_split_goal_1.
Proof.
  pre_process; simpl in *; entailer!.
  eapply best_prefix_state_153_step_update with
    (best_idx := best_idx) (max_strength := max).
  - exact PreH15.
  - destruct PreH12 as [Hlen _]; lia.
  - exact PreH7.
  - lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_8_2 : Strongest_Extension_entail_wit_8_2.
Proof.
  left.
  pre_process; simpl in *; entailer!.
  all: try solve [
    cancel
  | eapply best_prefix_state_153_step_update with
      (best_idx := best_idx) (max_strength := max);
    [exact PreH14 | destruct PreH11 as [Hlen _]; lia | exact PreH6 | lia]
  ].
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10_split_goal_1 : Strongest_Extension_entail_wit_10_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10_split_goal_2 : Strongest_Extension_entail_wit_10_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10_split_goal_3 : Strongest_Extension_entail_wit_10_split_goal_3.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10_split_goal_4 : Strongest_Extension_entail_wit_10_split_goal_4.
Proof.
  pre_process; simpl in *; entailer!.
  replace i with extensions_size_pre in PreH15 by lia.
  exact PreH15.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10_split_goal_spatial : Strongest_Extension_entail_wit_10_split_goal_spatial.
Proof.
  pre_process; simpl in *; entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre best_idx PreH12 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx : 0 <= best_idx < Zlength rows) by (destruct PreH12 as [Hlen _]; lia).
  rewrite (Znth_indep rows best_idx __default__List_Z nil) by exact Hidx.
  rewrite Hrow_len.
  rewrite Hrow_eq.
  rewrite row_payload_c_string_153.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_10 : Strongest_Extension_entail_wit_10.
Proof.
  left.
  pre_process_default.
  assert (Hi_end : i = extensions_size_pre) by lia.
  subst i.
  pose proof (rows_well_formed_153_row rows extensions_size_pre best_idx PreH10 ltac:(lia))
    as [Hrow_eq [Hvalid [Hlen_le [Hlen_lt Hrow_len]]]].
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    extensions_pre best_idx extensions_size_pre rows).
  - dump_pre_spatial. lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    rewrite sizeof_ptr.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil))
      with (CharArray.full row_ptr
        (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil)).
    rewrite Hrow_len.
    rewrite Hrow_eq.
    rewrite row_payload_c_string_153.
    unfold store_string.
    entailer!.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13_split_goal_1 : Strongest_Extension_entail_wit_13_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13_split_goal_2 : Strongest_Extension_entail_wit_13_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13_split_goal_3 : Strongest_Extension_entail_wit_13_split_goal_3.
Proof.
  pre_process; simpl in *; entailer!.
  destruct PreH10 as [Hall _].
  exact Hall.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13_split_goal_4 : Strongest_Extension_entail_wit_13_split_goal_4.
Proof.
  pre_process; simpl in *; entailer!.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13_split_goal_spatial : Strongest_Extension_entail_wit_13_split_goal_spatial.
Proof.
  pre_process; simpl in *; entailer!.
  rewrite PreH7.
  sep_apply_l_atomic (CharArray.full_split_to_seg class_name_pre
    (string_length class_l) (string_length class_l + 1) (c_string class_l)).
  - apply derivable1s_coq_prop_r.
    pose proof (string_length_nonneg class_l).
    lia.
  - sep_apply_l_atomic (CharArray.undef_full_split_to_undef_seg retval_2
      (string_length class_l) ((string_length class_l + retval) + 2)).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg class_l).
      pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
    + rewrite c_string_payload_prefix_153.
      rewrite c_string_null_suffix_153.
      sep_apply_l_atomic (CharArray.seg_to_full class_name_pre 0
        (string_length class_l) class_l).
      sep_apply_l_atomic (CharArray.undef_seg_to_undef_full retval_2 0
        (string_length class_l)).
      replace (class_name_pre + 0 * sizeof(CHAR)) with class_name_pre by lia.
      replace (string_length class_l - 0) with (string_length class_l) by lia.
      replace (retval_2 + 0 * sizeof(CHAR)) with retval_2 by lia.
      replace (string_length class_l - 0) with (string_length class_l) by lia.
      cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_13 : Strongest_Extension_entail_wit_13.
Proof.
  left.
  solve_153.
  - rewrite PreH7.
    unfold store_string.
    sep_apply_l_atomic (CharArray.full_split_to_seg class_name_pre
      (string_length class_l) (string_length class_l + 1) (c_string class_l)).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg class_l).
      lia.
    + sep_apply_l_atomic (CharArray.undef_full_split_to_undef_seg retval_2
        (string_length class_l) ((string_length class_l + retval) + 2)).
      * apply derivable1s_coq_prop_r.
        pose proof (string_length_nonneg class_l).
        pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
        lia.
      * rewrite c_string_payload_prefix_153.
        rewrite c_string_null_suffix_153.
        sep_apply_l_atomic (CharArray.seg_to_full class_name_pre 0
          (string_length class_l) class_l).
        sep_apply_l_atomic (CharArray.undef_seg_to_undef_full retval_2 0
          (string_length class_l)).
        replace (class_name_pre + 0 * sizeof(CHAR)) with class_name_pre by lia.
        replace (string_length class_l - 0) with (string_length class_l) by lia.
        replace (retval_2 + 0 * sizeof(CHAR)) with retval_2 by lia.
        replace (string_length class_l - 0) with (string_length class_l) by lia.
        cancel.
  - destruct PreH10 as [Hall _].
    exact Hall.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_14_split_goal_1 : Strongest_Extension_entail_wit_14_split_goal_1.
Proof.
  pre_process.
  simpl in *.
  entailer!.
  unfold row_len_z_153 in PreH6.
  pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
  lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_14_split_goal_spatial : Strongest_Extension_entail_wit_14_split_goal_spatial.
Proof.
  pre_process.
  simpl in *.
  subst retval.
  unfold c_string.
  rewrite PreH5.
  sep_apply_l_atomic (CharArray.full_to_seg class_name_pre
    (string_length class_l) class_l).
  sep_apply_l_atomic (CharArray.seg_merge_to_full class_name_pre 0
    (string_length class_l) (string_length class_l + 1)
    class_l (cons 0 nil)).
  - apply derivable1s_coq_prop_r.
    pose proof (string_length_nonneg class_l).
    lia.
  - sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_seg out
      (string_length class_l) (string_length class_l + 1)
      ((string_length class_l + n2) + 2)).
    + apply derivable1s_coq_prop_r.
      unfold row_len_z_153 in PreH6.
      pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
    + replace (class_name_pre + 0 * sizeof(CHAR)) with class_name_pre by lia.
      replace (string_length class_l + 1 - 0) with (string_length class_l + 1) by lia.
      cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_14 : Strongest_Extension_entail_wit_14.
Proof.
  right.
  solve_153.
  - subst retval.
    unfold c_string.
    rewrite PreH5.
    sep_apply_l_atomic (CharArray.full_to_seg class_name_pre
      (string_length class_l) class_l).
    sep_apply_l_atomic (CharArray.seg_merge_to_full class_name_pre 0
      (string_length class_l) (string_length class_l + 1)
      class_l (cons 0 nil)).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg class_l).
      lia.
    + sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_seg out
        (string_length class_l) (string_length class_l + 1)
        ((string_length class_l + n2) + 2)).
      * apply derivable1s_coq_prop_r.
        unfold row_len_z_153 in PreH6.
        pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
        lia.
      * replace (class_name_pre + 0 * sizeof(CHAR)) with class_name_pre by lia.
        replace (string_length class_l + 1 - 0) with (string_length class_l + 1) by lia.
        cancel.
  - unfold row_len_z_153 in PreH6.
    pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
    lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_15_split_goal_1 : Strongest_Extension_entail_wit_15_split_goal_1.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_15_split_goal_2 : Strongest_Extension_entail_wit_15_split_goal_2.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_15_split_goal_3 : Strongest_Extension_entail_wit_15_split_goal_3.
Proof. solve_153. Qed.
Lemma proof_of_Strongest_Extension_entail_wit_15_split_goal_spatial : Strongest_Extension_entail_wit_15_split_goal_spatial.
Proof.
  pre_process.
  simpl in *.
  unfold row_len_z_153 in PreH7.
  rewrite PreH7.
  sep_apply_l_atomic (CharArray.full_split_to_seg row_ptr
    (string_length (row_payload_z_153 (Znth best_idx rows nil)))
    (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth best_idx rows nil)))).
  - apply derivable1s_coq_prop_r.
    pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
    lia.
  - rewrite c_string_payload_prefix_153.
    rewrite c_string_null_suffix_153.
    sep_apply_l_atomic (CharArray.seg_to_full row_ptr 0
      (string_length (row_payload_z_153 (Znth best_idx rows nil)))
      (row_payload_z_153 (Znth best_idx rows nil))).
    sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_seg out
      (n1 + 1) ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)
      ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 2)).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
    + sep_apply_l_atomic (CharArray.undef_seg_to_undef_full out
        (n1 + 1) ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)).
      replace ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1) - (n1 + 1))
        with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
      replace (row_ptr + 0 * sizeof(CHAR)) with row_ptr by lia.
      replace (string_length (row_payload_z_153 (Znth best_idx rows nil)) - 0)
        with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
      cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_15 : Strongest_Extension_entail_wit_15.
Proof.
  left.
  solve_153.
  - rewrite (CharArray.undef_seg_empty out (n1 + 1)).
    unfold store_string.
    unfold row_len_z_153 in PreH7.
    rewrite PreH7.
    sep_apply_l_atomic (CharArray.full_split_to_seg row_ptr
      (string_length (row_payload_z_153 (Znth best_idx rows nil)))
      (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1)
      (c_string (row_payload_z_153 (Znth best_idx rows nil)))).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
    + rewrite c_string_payload_prefix_153.
      rewrite c_string_null_suffix_153.
      sep_apply_l_atomic (CharArray.seg_to_full row_ptr 0
        (string_length (row_payload_z_153 (Znth best_idx rows nil)))
        (row_payload_z_153 (Znth best_idx rows nil))).
      sep_apply_l_atomic (CharArray.undef_seg_split_to_undef_seg out
        (n1 + 1) ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)
        ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 2)).
      * apply derivable1s_coq_prop_r.
        pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
        lia.
      * sep_apply_l_atomic (CharArray.undef_seg_to_undef_full out
          (n1 + 1) ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)).
        replace ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1) - (n1 + 1))
          with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
        replace (row_ptr + 0 * sizeof(CHAR)) with row_ptr by lia.
        replace (string_length (row_payload_z_153 (Znth best_idx rows nil)) - 0)
          with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
        cancel.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_16_split_goal_spatial : Strongest_Extension_entail_wit_16_split_goal_spatial.
Proof.
  pre_process.
  simpl in *.
  unfold row_len_z_153 in PreH7.
  rewrite PreH7.
  unfold c_string.
  sep_apply_l_atomic (CharArray.full_to_seg row_ptr
    (string_length (row_payload_z_153 (Znth best_idx rows nil)))
    (row_payload_z_153 (Znth best_idx rows nil))).
  sep_apply_l_atomic (CharArray.seg_merge_to_full row_ptr 0
    (string_length (row_payload_z_153 (Znth best_idx rows nil)))
    (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1)
    (row_payload_z_153 (Znth best_idx rows nil)) (cons 0 nil)).
  - apply derivable1s_coq_prop_r.
    pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
    lia.
  - replace (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
      (string_length (row_payload_z_153 (Znth best_idx rows nil)))
      (row_payload_z_153 (Znth best_idx rows nil)))
      with (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
        (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
        (row_payload_z_153 (Znth best_idx rows nil))).
    2: {
      replace (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
        with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
      reflexivity.
    }
    sep_lift_L
      ((CharArray.full out (n1 + 1) (app class_l (cons 46 nil))) ::
       (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
          (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
          (row_payload_z_153 (Znth best_idx rows nil))) :: nil).
    sep_apply (CharArray.full_merge_to_full out (n1 + 1)
      ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)
      (app class_l (cons 46 nil)) (row_payload_z_153 (Znth best_idx rows nil))).
    + replace (row_ptr + 0 * sizeof(CHAR)) with row_ptr by lia.
      replace (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1 - 0)
        with (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1) by lia.
      cancel.
    + pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_16 : Strongest_Extension_entail_wit_16.
Proof.
  left.
  solve_153.
  - unfold store_string.
    unfold row_len_z_153 in PreH7.
    rewrite PreH7.
    unfold c_string.
    sep_apply_l_atomic (CharArray.full_to_seg row_ptr
      (string_length (row_payload_z_153 (Znth best_idx rows nil)))
      (row_payload_z_153 (Znth best_idx rows nil))).
    sep_apply_l_atomic (CharArray.seg_merge_to_full row_ptr 0
      (string_length (row_payload_z_153 (Znth best_idx rows nil)))
      (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1)
      (row_payload_z_153 (Znth best_idx rows nil)) (cons 0 nil)).
    + apply derivable1s_coq_prop_r.
      pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
      lia.
    + replace (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
        (string_length (row_payload_z_153 (Znth best_idx rows nil)))
        (row_payload_z_153 (Znth best_idx rows nil)))
        with (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
          (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
          (row_payload_z_153 (Znth best_idx rows nil))).
      2: {
        replace (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
          with (string_length (row_payload_z_153 (Znth best_idx rows nil))) by lia.
        reflexivity.
      }
      sep_lift_L
        ((CharArray.full out (n1 + 1) (app class_l (cons 46 nil))) ::
         (CharArray.full (out + (n1 + 1) * sizeof(CHAR))
            (((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1) - (n1 + 1))
            (row_payload_z_153 (Znth best_idx rows nil))) :: nil).
      sep_apply (CharArray.full_merge_to_full out (n1 + 1)
        ((n1 + string_length (row_payload_z_153 (Znth best_idx rows nil))) + 1)
        (app class_l (cons 46 nil)) (row_payload_z_153 (Znth best_idx rows nil))).
      * replace (row_ptr + 0 * sizeof(CHAR)) with row_ptr by lia.
        replace (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1 - 0)
          with (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1) by lia.
        cancel.
      * pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
        lia.
Qed.
Lemma proof_of_Strongest_Extension_entail_wit_17_split_goal_1 : Strongest_Extension_entail_wit_17_split_goal_1.
Proof.
  pre_process.
  simpl in *.
  entailer!.
  eapply best_prefix_state_153_problem_spec; eauto.
Qed.

Lemma proof_of_Strongest_Extension_entail_wit_17_split_goal_spatial : Strongest_Extension_entail_wit_17_split_goal_spatial.
Proof.
  pre_process.
  simpl in *.
  unfold output_payload_153, c_string, string_length.
  unfold row_len_z_153, string_length in PreH8.
  rewrite PreH7.
  unfold string_length.
  rewrite PreH8.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
  replace (Zlength class_l + Zlength (row_payload_z_153 (Znth best_idx rows nil)) + 1 + 1)
    with (Zlength class_l + (Z.succ 0 + Zlength (row_payload_z_153 (Znth best_idx rows nil))) + 1) by lia.
  rewrite !app_assoc.
  cancel.
Qed.

Lemma proof_of_Strongest_Extension_entail_wit_17 : Strongest_Extension_entail_wit_17.
Proof.
  right.
  solve_153.
  - unfold output_payload_153, c_string, string_length.
    unfold row_len_z_153, string_length in PreH8.
    rewrite PreH7.
    unfold string_length.
    rewrite PreH8.
    rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    replace (Zlength class_l + Zlength (row_payload_z_153 (Znth best_idx rows nil)) + 1 + 1)
      with (Zlength class_l + (Z.succ 0 + Zlength (row_payload_z_153 (Znth best_idx rows nil))) + 1) by lia.
    rewrite !app_assoc.
    cancel.
Qed.
Lemma proof_of_Strongest_Extension_return_wit_1 : Strongest_Extension_return_wit_1.
Proof.
  pre_process_default.
  Exists out_l_2.
  entailer!.
  pose proof (rows_well_formed_153_row rows extensions_size_pre best_idx PreH9 ltac:(lia))
    as [Hrow_eq [_ [_ [_ Hrow_len]]]].
  assert (Hidx : 0 <= best_idx < extensions_size_pre) by lia.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    extensions_pre best_idx extensions_size_pre row_ptr rows (Znth best_idx rows nil) Hidx) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  try rewrite sizeof_ptr in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil))
    with (CharArray.full row_ptr
      (Zlength (Znth best_idx rows nil)) (Znth best_idx rows nil)) in Hmerge.
  rewrite Hrow_len in Hmerge.
  rewrite Hrow_eq in Hmerge.
  rewrite row_payload_c_string_153 in Hmerge.
  unfold store_string.
  unfold StorePtrAsElement.storeA.
  rewrite sizeof_ptr.
  sepcon_lift (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows).
  sepcon_lift (CharArray.full row_ptr
    (string_length (row_payload_z_153 (Znth best_idx rows nil)) + 1)
    (c_string (row_payload_z_153 (Znth best_idx rows nil)))).
  sepcon_lift (((extensions_pre + best_idx * 4)) # Ptr |-> row_ptr).
  sep_apply Hmerge.
  rewrite <- Hrow_eq.
  rewrite replace_Znth_Znth by lia.
  cancel.
Qed.
Lemma proof_of_Strongest_Extension_partial_solve_wit_5_pure_split_goal_1 : Strongest_Extension_partial_solve_wit_5_pure_split_goal_1.
Proof.
  pre_process.
  simpl in *.
  entailer!.
  rewrite PreH15.
  rewrite PreH20.
  pose proof (string_length_nonneg class_l).
  pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
  lia.
Qed.
Lemma proof_of_Strongest_Extension_partial_solve_wit_5_pure : Strongest_Extension_partial_solve_wit_5_pure.
Proof.
  right.
  pre_process.
  simpl in *.
  entailer!.
  rewrite PreH15.
  rewrite PreH20.
  pose proof (string_length_nonneg class_l).
  pose proof (string_length_nonneg (row_payload_z_153 (Znth best_idx rows nil))).
  lia.
Qed.
