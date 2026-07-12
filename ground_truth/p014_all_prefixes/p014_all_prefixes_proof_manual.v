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
From SimpleC.EE.CAV.ground_truth_p014_all_prefixes Require Import p014_all_prefixes_goal.
From SimpleC.EE.CAV.ground_truth_p014_all_prefixes Require Import p014_all_prefixes_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p014_all_prefixes.
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



Lemma sublist_0_firstn_14 : forall {A : Type} hi (l : list A),
  0 <= hi ->
  sublist 0 hi l = firstn (Z.to_nat hi) l.
Proof.
  intros A hi l _.
  unfold sublist.
  reflexivity.
Qed.

Lemma prefix_payloads_nat_14_length : forall s n,
  List.length (prefix_payloads_nat_14 s n) = n.
Proof.
  induction n as [| n IH]; simpl; auto.
  rewrite app_length; simpl; lia.
Qed.

Lemma prefix_rows_heap_14_nil :
  emp |-- prefix_rows_heap_14 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma prefix_rows_heap_14_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  prefix_rows_heap_14 ptrs rows ** CharArray.full p (Zlength row) row
  |-- prefix_rows_heap_14 (ptrs ++ [p]) (rows ++ [row]).
Proof.
  intros ptrs rows p row Hlen.
  revert rows Hlen.
  induction ptrs as [| p0 ptrs IH]; intros rows Hlen;
    destruct rows as [| row0 rows]; simpl in *.
  - rewrite derivable1_sepcon_comm.
    entailer!.
  - exfalso.
    rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg rows). lia.
  - exfalso.
    rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg ptrs). lia.
  - rewrite Zlength_cons in Hlen.
    rewrite Zlength_cons in Hlen.
    assert (Htail : Zlength ptrs = Zlength rows) by lia.
    sep_apply (IH rows Htail).
    cancel.
Qed.

Lemma chararray_adjacent_segs_to_full_14 : forall p mid hi l1 l2,
  0 <= mid <= hi ->
  CharArray.seg p 0 mid l1 ** CharArray.seg p mid hi l2
  |-- CharArray.full p hi (l1 ++ l2).
Proof.
  intros p mid hi l1 l2 Hbounds.
  sep_apply (CharArray.seg_merge_to_seg p 0 mid hi l1 l2 Hbounds).
  sep_apply_l_atomic (CharArray.seg_to_full p 0 hi (l1 ++ l2)).
  replace (p + 0 * sizeof(CHAR)) with p by lia.
  replace (hi - 0) with hi by lia.
  entailer!.
Qed.

Lemma String_length_string_of_list_z_14 : forall l,
  String.length (string_of_list_z_14 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma Zlength_prefix_row_payload_14 : forall s i,
  0 <= i < string_length s ->
  Zlength (prefix_row_payload_14 s i) = i + 1.
Proof.
  intros s i Hi.
  unfold prefix_row_payload_14, string_length in *.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma all_ascii_prefix_row_payload_14 : forall s i,
  all_ascii s ->
  0 <= i < string_length s ->
  all_ascii (prefix_row_payload_14 s i).
Proof.
  intros s i Hascii Hi k Hk.
  pose proof (Zlength_prefix_row_payload_14 s i Hi) as Hlen.
  unfold prefix_row_payload_14.
  rewrite Znth_sublist0 by lia.
  apply Hascii.
  unfold string_length in Hi.
  lia.
Qed.

Lemma prefix_row_payload_c_string_14 : forall s i,
  0 <= i < string_length s ->
  sublist 0 (i + 1) (c_string s) = prefix_row_payload_14 s i.
Proof.
  intros s i Hi.
  unfold prefix_row_payload_14, c_string, string_length in *.
  apply sublist_split_app_l; lia.
Qed.

Lemma prefix_row_payload_suffix_c_string_14 : forall s i n,
  0 <= i < n ->
  n = string_length s ->
  prefix_row_payload_14 s i ++ sublist (i + 1) (n + 1) (c_string s) =
  c_string s.
Proof.
  intros s i n Hi Hn.
  subst n.
  rewrite <- (prefix_row_payload_c_string_14 s i) by lia.
  rewrite <- (sublist_split 0 (string_length s + 1) (i + 1) (c_string s)).
  2: lia.
  2: {
    assert (Hc_len : Zlength (c_string s) = string_length s + 1).
    {
      unfold c_string, string_length.
      rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
    }
    rewrite Hc_len.
    pose proof (Zlength_nonneg s).
    lia.
  }
  unfold c_string, string_length.
  rewrite sublist_self.
  - reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    lia.
Qed.

Lemma prefix_rows_state_14_initial : forall s,
  prefix_rows_state_14 s 0 nil.
Proof.
  intros s.
  unfold prefix_rows_state_14, prefix_rows_14, string_length.
  split; [rewrite Zlength_correct; lia|].
  reflexivity.
Qed.

Lemma prefix_payloads_nat_14_snoc : forall s n,
  prefix_payloads_nat_14 s (S n) =
  prefix_payloads_nat_14 s n ++ [firstn (S n) s].
Proof.
  reflexivity.
Qed.

Lemma prefix_rows_14_step : forall s i,
  0 <= i < string_length s ->
  prefix_rows_14 s (i + 1) =
  prefix_rows_14 s i ++ [prefix_row_14 s i].
Proof.
  intros s i Hi.
  unfold prefix_rows_14, prefix_row_14, prefix_row_payload_14.
  assert (Hsucc: Z.to_nat (i + 1) = S (Z.to_nat i)).
  {
    apply Nat2Z.inj.
    rewrite Z2Nat.id by lia.
    rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    lia.
  }
  rewrite Hsucc.
  simpl.
  rewrite map_app.
  simpl.
  rewrite sublist_0_firstn_14 by lia.
  rewrite Hsucc.
  reflexivity.
Qed.

Lemma prefix_rows_state_14_step : forall s i rows,
  prefix_rows_state_14 s i rows ->
  0 <= i < string_length s ->
  prefix_rows_state_14 s (i + 1) (rows ++ [prefix_row_14 s i]).
Proof.
  intros s i rows [Hbounds Hrows] Hi.
  split; [lia|].
  subst rows.
  symmetry.
  apply prefix_rows_14_step; exact Hi.
Qed.

Lemma Zlength_prefix_rows_14 : forall s n,
  0 <= n ->
  Zlength (prefix_rows_14 s n) = n.
Proof.
  intros s n Hn.
  unfold prefix_rows_14.
  rewrite Zlength_correct, map_length, prefix_payloads_nat_14_length.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma prefix_rows_state_14_Zlength : forall s n rows,
  prefix_rows_state_14 s n rows ->
  Zlength rows = n.
Proof.
  intros s n rows [Hbounds Hrows].
  subst rows.
  apply Zlength_prefix_rows_14.
  lia.
Qed.

Lemma row_payload_c_string_14 : forall payload,
  row_payload_z_14 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_14, c_string.
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

Lemma row_string_prefix_row_14 : forall s i,
  row_string_z_14 (prefix_row_14 s i) =
  string_of_list_z_14 (prefix_row_payload_14 s i).
Proof.
  intros s i.
  unfold row_string_z_14, prefix_row_14.
  rewrite row_payload_c_string_14.
  reflexivity.
Qed.

Lemma rows_to_strings_prefix_rows_14 : forall s n,
  rows_to_strings_z_14 (prefix_rows_14 s n) =
  map string_of_list_z_14 (prefix_payloads_nat_14 s (Z.to_nat n)).
Proof.
  intros s n.
  unfold rows_to_strings_z_14, prefix_rows_14.
  rewrite map_map.
  apply map_ext.
  intros payload.
  unfold row_string_z_14.
  rewrite row_payload_c_string_14.
  reflexivity.
Qed.

Lemma string_of_list_z_14_firstn_prefix : forall s n,
  String.prefix
    (string_of_list_z_14 (firstn n s))
    (string_of_list_z_14 s) = true.
Proof.
  induction s as [| c rest IH]; intros [| n]; simpl; auto.
  destruct (ascii_dec (ascii_of_z_14 c) (ascii_of_z_14 c)).
  - apply IH.
  - contradiction.
Qed.

Lemma nth_map_prefix_payloads_nat_14 : forall s n i,
  (i < n)%nat ->
  nth i
    (map string_of_list_z_14 (prefix_payloads_nat_14 s n))
    "0" =
  string_of_list_z_14 (firstn (S i) s).
Proof.
  induction n as [| n IH]; intros i Hi; [lia|].
  rewrite prefix_payloads_nat_14_snoc, map_app.
  destruct (Nat.eq_dec i n) as [Heq|Hneq].
  - subst i.
    rewrite app_nth2.
    + rewrite map_length, prefix_payloads_nat_14_length.
      replace (n - n)%nat with O by lia.
      reflexivity.
    + rewrite map_length, prefix_payloads_nat_14_length; lia.
  - rewrite app_nth1.
    + apply IH; lia.
    + rewrite map_length, prefix_payloads_nat_14_length; lia.
Qed.

Lemma prefix_rows_14_spec : forall s rows,
  prefix_rows_state_14 s (string_length s) rows ->
  problem_14_spec_z s rows.
Proof.
  intros s rows [Hbounds Hrows].
  unfold problem_14_spec_z, problem_14_spec.
  subst rows.
  rewrite rows_to_strings_prefix_rows_14.
  assert (Hznat: Z.to_nat (string_length s) = List.length s).
  {
    unfold string_length.
    rewrite Zlength_correct, Nat2Z.id.
    reflexivity.
  }
  rewrite Hznat.
  rewrite String_length_string_of_list_z_14.
  destruct (List.length s) as [| len] eqn:Hlen.
  - left.
    split; reflexivity.
  - right.
    split.
    + lia.
    + split.
      * rewrite map_length, prefix_payloads_nat_14_length.
        reflexivity.
      * intros i Hi.
        rewrite nth_map_prefix_payloads_nat_14 by lia.
        split.
        -- rewrite String_length_string_of_list_z_14.
           rewrite firstn_length.
           lia.
        -- apply string_of_list_z_14_firstn_prefix.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Lemma proof_of_all_prefixes_entail_wit_1 : all_prefixes_entail_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists (@nil Z) (@nil (list Z)).
    sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 retval).
    rewrite PtrArray.seg_empty.
    unfold store_string.
    entailer!.
    all: try apply prefix_rows_state_14_initial.
    all: try rewrite Zlength_nil; try lia.
    subst retval.
    apply string_length_nonneg.
Qed.

Lemma proof_of_all_prefixes_entail_wit_2 : all_prefixes_entail_wit_2.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    replace (string_length str_l + 1) with (n + 1) by lia.
    sep_apply_l_atomic (CharArray.full_split_to_seg
      str_pre (i + 1) (n + 1) (c_string str_l)).
    + dump_pre_spatial. unfold string_length in *. lia.
    + sep_apply_l_atomic (CharArray.seg_to_full str_pre 0 (i + 1)
        (sublist 0 (i + 1) (c_string str_l))).
      sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval (i + 2)).
      sep_apply (CharArray.undef_seg_split_to_undef_seg
        retval 0 (i + 1) (i + 2)).
      sep_apply_l_atomic (CharArray.undef_seg_to_undef_full retval 0 (i + 1)).
      replace (str_pre + 0 * sizeof(CHAR)) with str_pre by lia.
      replace (retval + 0 * sizeof(CHAR)) with retval by lia.
      replace (i + 1 - 0) with (i + 1) by lia.
      assert (Hi_str : 0 <= i < string_length str_l) by (subst n; lia).
      rewrite prefix_row_payload_c_string_14 by exact Hi_str.
      entailer!.
      * destruct PreH10 as [Hascii _].
        exact (all_ascii_prefix_row_payload_14 str_l i Hascii Hi_str).
      * exact (Zlength_prefix_row_payload_14 str_l i Hi_str).
      * lia.
Qed.

Lemma proof_of_all_prefixes_entail_wit_3 : all_prefixes_entail_wit_3.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string.
    sep_apply (CharArray.full_to_seg
      str_pre (i + 1) (prefix_row_payload_14 str_l i)).
    assert (Hi_str : 0 <= i < string_length str_l) by (subst n; lia).
    sep_apply (chararray_adjacent_segs_to_full_14
      str_pre (i + 1) (n + 1)
      (prefix_row_payload_14 str_l i)
      (sublist (i + 1) (n + 1) (c_string str_l))).
    replace (n + 1) with (string_length str_l + 1) by lia.
    entailer!.
    + replace (string_length str_l + 1) with (n + 1) by lia.
      pose proof (prefix_row_payload_suffix_c_string_14 str_l i n ltac:(lia) PreH4)
        as Hsuffix.
      rewrite <- Hsuffix at 2.
      entailer!.
    + lia.
Qed.

Lemma proof_of_all_prefixes_entail_wit_4 : all_prefixes_entail_wit_4.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    unfold store_string, prefix_row_14.
    replace ((i + 1) + 1) with (i + 2) by lia.
    replace ((prefix_row_payload_14 str_l i ++ 0 :: nil)%list)
      with (c_string (prefix_row_payload_14 str_l i)) by reflexivity.
    rewrite CharArray.undef_seg_empty.
    entailer!.
Qed.

Lemma proof_of_all_prefixes_entail_wit_5 : all_prefixes_entail_wit_5.
Proof.
  constructor.
  - pre_process_default.
    Exists ((output_ptrs_2 ++ (cur :: nil))%list)
      ((output_rows_2 ++ (prefix_row_14 str_l i :: nil))%list).
    replace (i + 2) with (Zlength (prefix_row_14 str_l i)).
    2: {
      unfold prefix_row_14, naive_C_Rules.c_string.
      rewrite Zlength_app_cons.
      assert (Hi_str : 0 <= i < string_length str_l) by lia.
      pose proof (Zlength_prefix_row_payload_14 str_l i Hi_str) as Hpayload_len.
      rewrite Hpayload_len.
      lia.
    }
    assert (Hrows_len : Zlength output_ptrs_2 = Zlength output_rows_2) by lia.
    sep_apply (prefix_rows_heap_14_app_single
      output_ptrs_2 output_rows_2 cur (prefix_row_14 str_l i) Hrows_len).
    unfold store_string.
      entailer!.
      * rewrite Zlength_app_cons. lia.
      * rewrite Zlength_app_cons. lia.
      * assert (Hi_str : 0 <= i < string_length str_l) by lia.
        exact (prefix_rows_state_14_step str_l i output_rows_2 PreH13 Hi_str).
Qed.

Lemma proof_of_all_prefixes_entail_wit_7 : all_prefixes_entail_wit_7.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2.
    replace i with n by lia.
    rewrite PtrArray.undef_seg_empty.
    entailer!.
    assert (Hstate_final :
      prefix_rows_state_14 str_l (string_length str_l) output_rows_2).
    {
      replace (string_length str_l) with i by lia.
      exact PreH11.
    }
    exact (prefix_rows_14_spec str_l output_rows_2 Hstate_final).
    replace n with i by lia.
    exact PreH11.
Qed.

Lemma proof_of_all_prefixes_return_wit_1 : all_prefixes_return_wit_1.
Proof.
  constructor.
  - pre_process_default.
    Exists output_ptrs_2 output_rows_2 data_2.
    replace (string_length str_l) with n by lia.
    entailer!.
Qed.

Lemma proof_of_all_prefixes_partial_solve_wit_3_pure_split_goal_1 : all_prefixes_partial_solve_wit_3_pure_split_goal_1.
Proof.
  pre_process_default.
  entailer!.
  subst retval.
  apply string_length_nonneg.
Qed.

Lemma proof_of_all_prefixes_partial_solve_wit_3_pure : all_prefixes_partial_solve_wit_3_pure.
Proof.
  constructor.
  - pre_process_default.
    entailer!.
    subst retval.
    apply string_length_nonneg.
Qed.
