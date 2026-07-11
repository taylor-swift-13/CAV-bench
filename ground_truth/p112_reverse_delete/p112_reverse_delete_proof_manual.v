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
From SimpleC.EE.CAV.ground_truth_p112_reverse_delete Require Import p112_reverse_delete_goal.
From SimpleC.EE.CAV.ground_truth_p112_reverse_delete Require Import p112_reverse_delete_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p112_reverse_delete.
Local Open Scope sac.

Ltac normalize112 :=
  repeat match goal with
  | H : ?x = ?y |- _ => subst x || subst y
  | |- context[signed_last_nbits ?x 8] =>
      rewrite (signed_last_nbits_eq x 8) by lia
  | H : context[signed_last_nbits ?x 8] |- _ =>
      rewrite (signed_last_nbits_eq x 8) in H by lia
  | |- context[Zlength (_ ++ _)] => rewrite Zlength_app
  | H : context[Zlength (_ ++ _)] |- _ => rewrite Zlength_app in H
  | |- context[Zlength (cons _ _)] => rewrite Zlength_cons
  | H : context[Zlength (cons _ _)] |- _ => rewrite Zlength_cons in H
  | |- context[Zlength (@nil _)] => rewrite Zlength_nil
  | H : context[Zlength (@nil _)] |- _ => rewrite Zlength_nil in H
  | |- context[Znth 0 (cons ?x ?xs) ?d] => rewrite Znth0_cons
  | H : context[Znth 0 (cons ?x ?xs) ?d] |- _ => rewrite Znth0_cons in H
  | |- context[Znth 1 (cons ?x (cons ?y ?ys)) ?d] =>
      rewrite Znth_cons by lia; rewrite Znth0_cons
  | H : context[Znth 1 (cons ?x (cons ?y ?ys)) ?d] |- _ =>
      rewrite Znth_cons in H by lia; rewrite Znth0_cons in H
  end; simpl in *.

Ltac spatial112 :=
  repeat match goal with
  | |- context[CharArray.full ?p 0 (@nil Z)] =>
      rewrite (CharArray.full_empty p 0)
	  | |- ?P |-- ?Q =>
	      match Q with
	      | context[CharArray.undef_seg ?p 0 ?n] =>
	          sep_apply_l_atomic (CharArray.undef_full_to_undef_seg p n)
	      end
	  | |- ?P |-- ?Q =>
	      match P with
	      | context[PtrArray.undef_missing_i ?p 0 0 2] =>
	          sep_apply_l_atomic (PtrArray.undef_missing_i_to_undef_seg_head p 0 2 ltac:(lia))
	      end
	  | |- ?P |-- ?Q =>
	      match P with
	      | context[((?p + (0 * sizeof(PTR))) # Ptr |-> ?v)] =>
	          sep_apply_l_atomic (PtrArray.seg_single p 0 v)
	      end
	  end.

Ltac add112_facts :=
  repeat match goal with
  | H : palindrome_scan_state_112 ?s ?i ?pal |- _ =>
      let Hpal := fresh "Hpal_bounds" in
      let Hpal1 := fresh "Hpal_mirror" in
      let Hpal0 := fresh "Hpal_mismatch" in
      let Hpalcase := fresh "Hpal_case" in
      destruct H as [Hpal [Hpal1 [Hpal0 Hpalcase]]]
  end;
  match goal with
  | H : filter_prefix_state_112 ?s ?c ?i ?out |- _ =>
      let Hlen := fresh "Hfilter_len" in
      pose proof (filter_prefix_state_112_length_le s c i out H) as Hlen
  | _ => idtac
  end.

Ltac solve112 :=
  constructor; pre_process_default; normalize112; add112_facts; normalize112; spatial112; normalize112;
  try solve [entailer!; normalize112; try apply filter_prefix_state_112_initial; try apply palindrome_scan_state_112_initial; try lia].

Ltac solve112_pure :=
  pre_process_default; normalize112; add112_facts; normalize112; spatial112; normalize112;
  try solve [entailer!; normalize112; try apply filter_prefix_state_112_initial; try apply palindrome_scan_state_112_initial; try lia].

Lemma proof_of_reverse_delete_safety_wit_20 : reverse_delete_safety_wit_20.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_safety_wit_21 : reverse_delete_safety_wit_21.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_safety_wit_22 : reverse_delete_safety_wit_22.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_safety_wit_23 : reverse_delete_safety_wit_23.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_safety_wit_28 : reverse_delete_safety_wit_28.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_safety_wit_29 : reverse_delete_safety_wit_29.
Proof. solve112. Qed.

Lemma proof_of_reverse_delete_entail_wit_1 : reverse_delete_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  normalize112; spatial112; normalize112.
  Exists (@nil Z).
  rewrite (CharArray.full_empty retval_2 0).
  entailer!.
  - apply filter_prefix_state_112_initial.
  - unfold string_length. apply Zlength_nonneg.
Qed.

Lemma proof_of_reverse_delete_entail_wit_2 : reverse_delete_entail_wit_2.
Proof.
  right.
  pre_process_default.
  normalize112; add112_facts; normalize112; spatial112; normalize112.
  assert (Hi_str : 0 <= i < string_length s_l) by lia.
  pose proof (valid_reverse_delete_input_112_s_char_range s_l c_l i PreH20 Hi_str) as Hchar_range_c.
  rewrite c_string_Znth_inside_112 in Hchar_range_c by exact Hi_str.
  destruct Hchar_range_c as [Hchar_range Hchar_nonzero].
  entailer!;
    try solve [lia];
    try solve [
      intro Hcmp;
      rewrite c_string_Znth_inside_112 in Hcmp by exact Hi_str;
      match type of Hcmp with
      | (?a ?= ?b)%Z = Gt =>
          pose proof (Z.compare_spec a b) as Hcmp_spec;
          rewrite Hcmp in Hcmp_spec;
          inversion Hcmp_spec;
          lia
      end
    ];
    try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  - unfold filter_prefix_state_112 in PreH24 |- *.
    destruct PreH24 as [Hprefix_bounds Hprefix_eq].
    split; [unfold string_length in *; lia|].
    rewrite sublist_0_succ_Z_112 by (unfold string_length in *; lia).
    rewrite filter_not_in_z_112_app_single_add.
    + rewrite <- Hprefix_eq.
      rewrite (signed_last_nbits_eq (Znth i (c_string s_l) 0) 8).
      * rewrite c_string_Znth_inside_112 by exact Hi_str.
        reflexivity.
      * lia.
      * simpl.
        rewrite c_string_Znth_inside_112 by exact Hi_str.
        destruct Hchar_range; lia.
    + apply char_in_zb_112_false_iff.
      apply (strchr_result_zero_not_in_112 c_l (Znth i s_l 0) c_pre).
      * rewrite <- c_string_Znth_inside_112 by exact Hi_str.
        exact PreH2.
      * exact Hchar_nonzero.
Qed.

Lemma proof_of_reverse_delete_entail_wit_3 : reverse_delete_entail_wit_3.
Proof.
  right.
  pre_process_default.
  normalize112; add112_facts; normalize112; spatial112; normalize112.
  assert (Hi_str : 0 <= i < string_length s_l) by lia.
  pose proof (valid_reverse_delete_input_112_s_char_range s_l c_l i PreH20 Hi_str) as Hchar_range_c.
  rewrite c_string_Znth_inside_112 in Hchar_range_c by exact Hi_str.
  destruct Hchar_range_c as [Hchar_range Hchar_nonzero].
  entailer!;
    try solve [lia];
    try solve [
      intro Hcmp;
      rewrite c_string_Znth_inside_112 in Hcmp by exact Hi_str;
      match type of Hcmp with
      | (?a ?= ?b)%Z = Gt =>
          pose proof (Z.compare_spec a b) as Hcmp_spec;
          rewrite Hcmp in Hcmp_spec;
          inversion Hcmp_spec;
          lia
      end
    ].
  - unfold filter_prefix_state_112 in PreH24 |- *.
    destruct PreH24 as [Hprefix_bounds Hprefix_eq].
    split; [unfold string_length in *; lia|].
    rewrite sublist_0_succ_Z_112 by (unfold string_length in *; lia).
    rewrite filter_not_in_z_112_app_single_skip.
    + exact Hprefix_eq.
    + apply char_in_zb_112_true_iff.
      rewrite <- c_string_Znth_inside_112 by exact Hi_str.
      apply (strchr_result_nonzero_in_112 c_l (Znth i (c_string s_l) 0) retval c_pre).
      * exact PreH2.
      * exact PreH1.
      * rewrite c_string_Znth_inside_112 by exact Hi_str.
        exact Hchar_nonzero.
Qed.

Lemma proof_of_reverse_delete_entail_wit_5 : reverse_delete_entail_wit_5.
Proof.
  left.
  pre_process_default.
  normalize112; spatial112; normalize112.
  Exists filtered_l_2.
  unfold store_string, c_string, string_length.
  entailer!.
  - assert (Hi_done : i = Zlength s_l) by (unfold string_length in *; lia).
    subst i.
    exact PreH22.
Qed.

Lemma proof_of_reverse_delete_entail_wit_6 : reverse_delete_entail_wit_6.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists filtered_l_2.
  subst pal.
  entailer!;
    try solve [apply palindrome_scan_state_112_initial];
    try solve [
      rewrite PreH2;
      apply Z.div_pos;
      [apply Zlength_nonneg|lia]
    ];
    try lia.
  - rewrite PreH2.
    apply Z.quot_pos.
    + apply Zlength_nonneg.
    + lia.
Qed.

Lemma proof_of_reverse_delete_entail_wit_7_1 : reverse_delete_entail_wit_7_1.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists filtered_l_2.
  subst pal.
  assert (Hk_nonneg : 0 <= k) by (rewrite PreH6; apply Zlength_nonneg).
  assert (Hquot_nonneg : 0 <= k ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hquot_le_k : k ÷ 2 <= k) by (apply Z.quot_le_upper_bound; lia).
  entailer!;
    try solve [lia].
  apply palindrome_scan_state_112_step_match.
  - exact PreH22.
  - split; [lia|rewrite <- PreH6; lia].
  - assert (Hi_in : 0 <= i < string_length filtered_l_2)
      by (unfold string_length; rewrite <- PreH6; lia).
    assert (Hmirror_in : 0 <= k - 1 - i < string_length filtered_l_2)
      by (unfold string_length; rewrite <- PreH6; lia).
    assert (Hi_payload :
      Znth i (c_string filtered_l_2) 0 = Znth i filtered_l_2 0)
      by (apply c_string_Znth_inside_112; exact Hi_in).
    assert (Hmirror_payload :
      Znth (k - 1 - i) (c_string filtered_l_2) 0 =
      Znth (k - 1 - i) filtered_l_2 0)
      by (apply c_string_Znth_inside_112; exact Hmirror_in).
    rewrite Hi_payload in PreH1.
    rewrite Hmirror_payload in PreH1.
    rewrite PreH6 in PreH1.
    exact PreH1.
Qed.

Lemma proof_of_reverse_delete_entail_wit_7_2 : reverse_delete_entail_wit_7_2.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros2].
  Exists filtered_l_2.
  subst pal.
  assert (Hk_nonneg : 0 <= k) by (rewrite PreH6; apply Zlength_nonneg).
  assert (Hquot_nonneg : 0 <= k ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hquot_le_k : k ÷ 2 <= k) by (apply Z.quot_le_upper_bound; lia).
  entailer!;
    try solve [lia].
  apply palindrome_scan_state_112_step_false.
  - exact PreH22.
  - split; [lia|rewrite <- PreH6; lia].
Qed.

Lemma proof_of_reverse_delete_entail_wit_8_1 : reverse_delete_entail_wit_8_1.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists filtered_l_2.
  subst pal.
  assert (Hk_nonneg : 0 <= k) by (rewrite PreH9; apply Zlength_nonneg).
  assert (Hquot_nonneg : 0 <= k ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hquot_le_k : k ÷ 2 <= k) by (apply Z.quot_le_upper_bound; lia).
  spatial112; simpl; unfold store_string.
  entailer!;
    try solve [lia].
  apply (palindrome_scan_state_112_false_extend filtered_l_2 i (k ÷ 2)).
  - exact PreH25.
  - split; [lia|rewrite <- PreH9; exact Hquot_le_k].
Qed.

Lemma proof_of_reverse_delete_entail_wit_8_2 : reverse_delete_entail_wit_8_2.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists filtered_l_2.
  subst pal.
  assert (Hk_nonneg : 0 <= k) by (rewrite PreH9; apply Zlength_nonneg).
  assert (Hquot_nonneg : 0 <= k ÷ 2) by (apply Z.quot_pos; lia).
  assert (Hquot_le_k : k ÷ 2 <= k) by (apply Z.quot_le_upper_bound; lia).
  assert (Hi_in : 0 <= i < string_length filtered_l_2)
    by (unfold string_length; rewrite <- PreH9; lia).
  assert (Hmirror_in : 0 <= k - 1 - i < string_length filtered_l_2)
    by (unfold string_length; rewrite <- PreH9; lia).
  assert (Hneq_payload :
    Znth i filtered_l_2 0 <>
    Znth (Zlength filtered_l_2 - 1 - i) filtered_l_2 0).
  {
    intro Heq.
    assert (Hi_payload :
      Znth i (c_string filtered_l_2) 0 = Znth i filtered_l_2 0)
      by (apply c_string_Znth_inside_112; exact Hi_in).
    assert (Hmirror_payload :
      Znth (k - 1 - i) (c_string filtered_l_2) 0 =
      Znth (k - 1 - i) filtered_l_2 0)
      by (apply c_string_Znth_inside_112; exact Hmirror_in).
    rewrite Hi_payload in PreH4.
    rewrite Hmirror_payload in PreH4.
    rewrite PreH9 in PreH4.
    contradiction.
  }
  spatial112; simpl; unfold store_string.
  entailer!;
    try solve [lia].
  eapply palindrome_scan_state_112_false_extend.
  - apply palindrome_scan_state_112_step_mismatch.
    + exact PreH25.
    + split; [lia|rewrite <- PreH9; lia].
    + exact Hneq_payload.
  - split; [lia|rewrite <- PreH9; exact Hquot_le_k].
Qed.

Lemma proof_of_reverse_delete_entail_wit_8_3 : reverse_delete_entail_wit_8_3.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  Exists filtered_l_2.
  subst pal.
  assert (Hi_done : i = k ÷ 2) by lia.
  subst i.
  spatial112; simpl; unfold store_string.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_8_4 : reverse_delete_entail_wit_8_4.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros2].
  Exists filtered_l_2.
  subst pal.
  assert (Hi_done : i = k ÷ 2) by lia.
  subst i.
  spatial112; simpl; unfold store_string.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_entail_wit_13_1 : reverse_delete_entail_wit_13_1.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros1].
  unfold string_length in *.
  subst n pal.
  assert (Hfiltered : filtered_l_2 = filter_not_in_z_112 s_l c_l).
  { apply filter_prefix_state_112_full. exact PreH20. }
  subst filtered_l_2.
  assert (Hpal : pal_bool_112 (filter_not_in_z_112 s_l c_l) = false).
  { rewrite PreH6 in PreH21.
    apply palindrome_scan_state_112_false_full. exact PreH21. }
  assert (Hrows :
    (c_string (filter_not_in_z_112 s_l c_l) :: bool_row_112 false :: nil) =
    reverse_delete_rows_112 s_l c_l).
  { unfold reverse_delete_rows_112. rewrite Hpal. reflexivity. }
  Exists (c_string (filter_not_in_z_112 s_l c_l) :: bool_row_112 false :: nil)
    (cons filtered (cons truth nil))
    (filter_not_in_z_112 s_l c_l).
  simpl.
  normalize112.
  try rewrite !c_string_Zlength_112.
  unfold store_string.
  unfold string_length.
  entailer!.
  - rewrite Hrows. apply problem_112_spec_z_reverse_delete_rows_112. exact PreH16.
Qed.

Lemma proof_of_reverse_delete_entail_wit_13_2 : reverse_delete_entail_wit_13_2.
Proof.
  pre_process_default.
  eapply derivable1_trans; [| apply derivable1_orp_intros2].
  unfold string_length in *.
  subst n pal.
  assert (Hfiltered : filtered_l_2 = filter_not_in_z_112 s_l c_l).
  { apply filter_prefix_state_112_full. exact PreH20. }
  subst filtered_l_2.
  assert (Hpal : pal_bool_112 (filter_not_in_z_112 s_l c_l) = true).
  { rewrite PreH6 in PreH21.
    apply palindrome_scan_state_112_true_full. exact PreH21. }
  assert (Hrows :
    (c_string (filter_not_in_z_112 s_l c_l) :: bool_row_112 true :: nil) =
    reverse_delete_rows_112 s_l c_l).
  { unfold reverse_delete_rows_112. rewrite Hpal. reflexivity. }
  Exists (c_string (filter_not_in_z_112 s_l c_l) :: bool_row_112 true :: nil)
    (cons filtered (cons truth nil))
    (filter_not_in_z_112 s_l c_l).
  simpl.
  normalize112.
  try rewrite !c_string_Zlength_112.
  unfold store_string.
  unfold string_length.
  entailer!.
  - rewrite Hrows. apply problem_112_spec_z_reverse_delete_rows_112. exact PreH16.
Qed.

Lemma proof_of_reverse_delete_return_wit_1 : reverse_delete_return_wit_1.
Proof.
  left.
  pre_process_default.
  Exists output_ptrs_2 output_rows_2 data_2.
  normalize112.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_return_wit_2 : reverse_delete_return_wit_2.
Proof.
  left.
  pre_process_default.
  Exists output_ptrs_2 output_rows_2 data_2.
  normalize112.
  entailer!.
Qed.

Lemma proof_of_reverse_delete_partial_solve_wit_2_pure : reverse_delete_partial_solve_wit_2_pure.
Proof.
  right.
  pre_process_default.
  unfold string_length in *.
  apply derivable1s_coq_prop_r.
  pose proof (Zlength_nonneg s_l).
  lia.
Qed.

Lemma proof_of_reverse_delete_partial_solve_wit_5_pure : reverse_delete_partial_solve_wit_5_pure.
Proof.
  right.
  pre_process_default.
  unfold string_length in *.
  assert (Hch_range :
    0 <= Znth i (c_string s_l) 0 <= 127 /\
    Znth i (c_string s_l) 0 <> 0).
  { apply (valid_reverse_delete_input_112_s_char_range s_l c_l i).
    - exact PreH30.
    - split; [exact PreH16 | subst n; exact PreH15]. }
  apply _derivable1_andp_intros.
  all: apply derivable1s_coq_prop_r; lia.
Qed.
