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
From SimpleC.EE.CAV.ground_truth_p125_split_words Require Import p125_split_words_goal.
From SimpleC.EE.CAV.ground_truth_p125_split_words Require Import p125_split_words_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p125_split_words.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import naive_C_Rules.
Local Open Scope sac.



Lemma contains_zb_125_true_of_Znth : forall s c i,
  0 <= i < Zlength s ->
  Znth i s 0 = c ->
  contains_zb_125 s c = true.
Proof.
  induction s as [|a s IH]; intros c i Hi Hnth.
  - rewrite Zlength_nil in Hi; lia.
  - simpl.
    destruct (Z.eqb_spec a c); [reflexivity|].
    rewrite Zlength_cons in Hi.
    assert (0 < i).
    {
      destruct (Z.eq_dec i 0) as [Hz | Hz].
      - subst i. unfold Znth in Hnth. simpl in Hnth. congruence.
      - lia.
    }
    apply IH with (i := i - 1).
    + lia.
    + rewrite Znth_cons in Hnth by lia.
      exact Hnth.
Qed.

Lemma contains_zb_125_false_of_forall : forall s c,
  (forall k, 0 <= k < Zlength s -> Znth k s 0 <> c) ->
  contains_zb_125 s c = false.
Proof.
  induction s as [|a s IH]; intros c Hnone.
  - reflexivity.
  - simpl.
    destruct (Z.eqb_spec a c) as [Heq | Hneq].
    + specialize (Hnone 0).
      unfold Znth in Hnone. simpl in Hnone.
      exfalso; apply Hnone.
      * rewrite Zlength_cons. pose proof (Zlength_nonneg s). lia.
      * exact Heq.
    + apply IH.
      intros k Hk.
      specialize (Hnone (k + 1)).
      rewrite Znth_cons in Hnone by lia.
      replace (k + 1 - 1) with k in Hnone by lia.
      apply Hnone.
      rewrite Zlength_cons in *.
      pose proof (Zlength_nonneg s). lia.
Qed.

Lemma strchr_result_nonzero_contains_zb_125 : forall s c ret p,
  c <> 0 ->
  ret <> 0 ->
  strchr_result s c ret p ->
  contains_zb_125 s c = true.
Proof.
  intros s c ret p Hc Hret Hres.
  destruct Hres as [[i [Hi [Hnth [_ [_ _]]]]] | [Hnone [[Hz _] | [_ Hzero]]]].
  - apply contains_zb_125_true_of_Znth with (i := i); auto.
  - contradiction.
  - contradiction.
Qed.

Lemma strchr_result_zero_contains_zb_125 : forall s c p,
  c <> 0 ->
  strchr_result s c 0 p ->
  contains_zb_125 s c = false.
Proof.
  intros s c p Hc Hres.
  destruct Hres as [[i [_ [_ [_ [_ Hnz]]]]] | [Hnone [[Hz _] | [_ Hzero]]]].
  - contradiction.
  - contradiction.
  - apply contains_zb_125_false_of_forall.
    unfold string_length in Hnone.
    exact Hnone.
Qed.

Lemma problem_125_spec_z_any : forall s rows,
  problem_125_spec_z s rows.
Proof.
  intros s rows.
  unfold problem_125_spec_z, problem_125_spec, output_sum_z_125,
    spec_contains_125, spec_split_125, spec_count_odd_lowercase_125.
  destruct (contains (list_ascii_of_string (string_of_list_z_125 s)) " "%char);
    [reflexivity|].
  destruct (contains (list_ascii_of_string (string_of_list_z_125 s)) ","%char);
    reflexivity.
Qed.

Lemma split_words_rows_heap_125_nil :
  emp |-- split_words_rows_heap_125 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma split_words_rows_heap_125_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  split_words_rows_heap_125 ptrs rows ** CharArray.full p (Zlength row) row
  |-- split_words_rows_heap_125 (ptrs ++ [p]) (rows ++ [row]).
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

Lemma Zlength_map_125 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  induction l as [| x xs IH].
  - reflexivity.
  - simpl.
    rewrite !Zlength_cons.
    lia.
Qed.

Lemma split_state_nat_125_step : forall i s sep,
  0 <= i ->
  split_state_nat_125 (Z.to_nat (i + 1)) s sep =
  split_step_125 sep (split_state_nat_125 (Z.to_nat i) s sep) (Znth i s 0).
Proof.
  intros i s sep Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma c_string_Znth_before_125 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma all_ascii_c_string_Znth_125 : forall s i,
  all_ascii s ->
  0 <= i < Zlength s ->
  0 <= Znth i (c_string s) 0 <= 127.
Proof.
  intros s i Hascii Hi.
  rewrite c_string_Znth_before_125 by lia.
  apply Hascii.
  exact Hi.
Qed.

Lemma word_payload_125_step : forall s start i,
  0 <= start /\ start <= i /\ i < Zlength s ->
  word_payload_125 s start (i + 1) =
  word_payload_125 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds.
  unfold word_payload_125.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry.
    apply sublist_single.
    lia.
Qed.

Lemma Zlength_word_payload_125 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (word_payload_125 s start stop) = stop - start.
Proof.
  intros s start stop Hbounds Hstop.
  unfold word_payload_125.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma word_payload_125_empty : forall s start,
  word_payload_125 s start start = [].
Proof.
  intros s start.
  unfold word_payload_125.
  apply sublist_nil.
  lia.
Qed.

Lemma word_payload_125_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  word_payload_125 s start (start + (k + 1)) =
  word_payload_125 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite word_payload_125_step by lia.
  rewrite c_string_Znth_before_125 by lia.
  reflexivity.
Qed.

Lemma word_row_125_unfold : forall s start stop,
  word_row_125 s start stop =
  word_payload_125 s start stop ++ [0].
Proof.
  intros.
  unfold word_row_125, c_string.
  reflexivity.
Qed.

Lemma split_scan_state_125_step_delim_nonempty : forall s i start sep rows,
  split_scan_state_125 s i start sep rows ->
  0 <= start < i ->
  Znth i s 0 = sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) (-1) sep
    (rows ++ [word_row_125 s start i]).
Proof.
  intros s i start sep rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart_bad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur as [| c cs].
    + simpl in Hcur.
      assert (Zlength (word_payload_125 s start i) = i - start).
      { apply Zlength_word_payload_125; lia. }
      rewrite <- Hcur in H.
      rewrite Zlength_nil in H.
      lia.
    + simpl.
      unfold word_row_125.
      rewrite map_app.
      rewrite Hcur.
      reflexivity.
  - left.
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; split; reflexivity.
Qed.

Lemma split_scan_state_125_step_delim_empty : forall s i sep rows,
  split_scan_state_125 s i (-1) sep rows ->
  Znth i s 0 = sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) (-1) sep rows.
Proof.
  intros s i sep rows Hstate Hdelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; [reflexivity|congruence].
  - left.
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur_empty.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_125.
    rewrite Hdelim.
    rewrite Z.eqb_refl.
    destruct cur; [split; reflexivity|congruence].
Qed.

Lemma split_scan_state_125_step_nondelim_continue : forall s i start sep rows,
  split_scan_state_125 s i start sep rows ->
  0 <= start < i ->
  Znth i s 0 <> sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) start sep rows.
Proof.
  intros s i start sep rows Hstate Hstart Hnondelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    rewrite Hcur.
    rewrite word_payload_125_step by lia.
    reflexivity.
Qed.

Lemma split_scan_state_125_step_nondelim_start : forall s i sep rows,
  split_scan_state_125 s i (-1) sep rows ->
  Znth i s 0 <> sep ->
  i < Zlength s ->
  split_scan_state_125 s (i + 1) i sep rows.
Proof.
  intros s i sep rows Hstate Hnondelim Hi.
  unfold split_scan_state_125 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_125, split_completed_payloads_125,
      split_scan_current_125 in *.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_125_step by lia.
    rewrite Hst.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_125.
    rewrite split_state_nat_125_step by lia.
    unfold split_scan_current_125 in Hcur_empty.
    destruct (split_state_nat_125 (Z.to_nat i) s sep) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_125.
    destruct (Z.eqb_spec (Znth i s 0) sep); [congruence|].
    subst cur.
    simpl.
    unfold word_payload_125.
    replace (sublist i (i + 1) s) with [Znth i s 0].
    + reflexivity.
    + symmetry; apply sublist_single; lia.
Qed.

Lemma split_scan_state_125_final_empty : forall s sep rows,
  split_scan_state_125 s (Zlength s) (-1) sep rows ->
  rows = split_output_rows_125 s sep.
Proof.
  intros s sep rows Hstate.
  unfold split_scan_state_125 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur Hstart] | [Hbad _]]; [| lia].
  subst rows.
  unfold split_output_rows_125, split_payloads_125,
    split_completed_rows_125, split_completed_payloads_125 in *.
  unfold split_scan_current_125 in Hcur.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [payloads cur].
  simpl in *.
  subst cur.
  reflexivity.
Qed.

Lemma split_scan_state_125_final_nonempty : forall s sep start rows,
  split_scan_state_125 s (Zlength s) start sep rows ->
  0 <= start < Zlength s ->
  rows ++ [word_row_125 s start (Zlength s)] = split_output_rows_125 s sep.
Proof.
  intros s sep start rows Hstate Hstart.
  unfold split_scan_state_125 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [_ Hcur]]; [lia|].
  subst rows.
  unfold split_output_rows_125, split_payloads_125,
    split_completed_rows_125, split_completed_payloads_125 in *.
  unfold split_scan_current_125 in Hcur.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [payloads cur].
  simpl in *.
  destruct cur as [| c cs].
  - assert (Zlength (word_payload_125 s start (Zlength s)) =
      Zlength s - start).
    { apply Zlength_word_payload_125; lia. }
    rewrite <- Hcur in H.
    rewrite Zlength_nil in H.
    lia.
  - unfold word_row_125.
    rewrite <- Hcur.
    simpl.
    rewrite map_app.
    reflexivity.
Qed.

Lemma split_state_nat_125_rows_bound : forall n s sep rows cur,
  split_state_nat_125 n s sep = (rows, cur) ->
  Zlength rows <= Z.of_nat n.
Proof.
  induction n as [| n IH]; intros s sep rows cur Hst; simpl in Hst.
  - inversion Hst; subst. rewrite Zlength_nil. lia.
  - destruct (split_state_nat_125 n s sep) as [rows0 cur0] eqn:Hprev.
    unfold split_step_125 in Hst.
    destruct (Z.eqb (Znth (Z.of_nat n) s 0) sep).
    + destruct cur0 as [| c cs]; inversion Hst; subst.
      * specialize (IH s sep rows [] Hprev). lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        specialize (IH s sep rows0 (c :: cs) Hprev). lia.
    + inversion Hst; subst.
      specialize (IH s sep rows cur0 Hprev).
      lia.
Qed.

Lemma Zlength_split_output_rows_125_le : forall s sep,
  Zlength (split_output_rows_125 s sep) <= Zlength s + 1.
Proof.
  intros s sep.
  unfold split_output_rows_125, split_payloads_125.
  destruct (split_state_nat_125 (Z.to_nat (Zlength s)) s sep) as [rows cur] eqn:Hst.
  destruct cur as [| c cs].
  - rewrite Zlength_map_125.
    pose proof (split_state_nat_125_rows_bound _ _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
  - rewrite Zlength_map_125, Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (split_state_nat_125_rows_bound _ _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
Qed.

Lemma odd_lower_count_payload_125_nonneg : forall s,
  0 <= odd_lower_count_payload_125 s.
Proof.
  induction s as [|c rest IH]; simpl.
  - lia.
  - destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma odd_lower_count_payload_125_le_Zlength : forall s,
  odd_lower_count_payload_125 s <= Zlength s.
Proof.
  induction s as [|c rest IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma list_ascii_of_string_string_of_list_z_125 : forall l,
  list_ascii_of_string (string_of_list_z_125 l) = map ascii_of_z_125 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma nat_of_ascii_ascii_of_z_125 : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of_z_125 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_125.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma ascii_eqb_ascii_of_z_const_125 : forall z n,
  0 <= z < 256 ->
  (n < 256)%nat ->
  Ascii.eqb (ascii_of_z_125 z) (ascii_of_nat n) = Z.eqb z (Z.of_nat n).
Proof.
  intros z n Hz Hn.
  destruct (Ascii.eqb_spec (ascii_of_z_125 z) (ascii_of_nat n)) as [Heq | Hneq];
    destruct (Z.eqb_spec z (Z.of_nat n)) as [Hz' | Hnz]; try reflexivity.
  - exfalso.
    apply Hnz.
    apply (f_equal nat_of_ascii) in Heq.
    rewrite nat_of_ascii_ascii_of_z_125 in Heq by exact Hz.
    rewrite nat_ascii_embedding in Heq by lia.
    lia.
  - subst z.
    exfalso.
    apply Hneq.
    unfold ascii_of_z_125.
    rewrite Nat2Z.id.
    reflexivity.
Qed.

Lemma contains_zb_125_false_ascii : forall s c n,
  all_ascii s ->
  c = Z.of_nat n ->
  (n < 256)%nat ->
  contains_zb_125 s c = false ->
  contains (map ascii_of_z_125 s) (ascii_of_nat n) = false.
Proof.
  induction s as [|x xs IH]; intros c n Hascii Hc Hn Hcontains.
  - reflexivity.
  - simpl in Hcontains.
    simpl.
    assert (Hx : 0 <= x < 256).
    {
      specialize (Hascii 0).
      rewrite Znth0_cons in Hascii.
      assert (0 <= 0 < Zlength (x :: xs)).
      { rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
      specialize (Hascii H).
      lia.
    }
    assert (Htail : all_ascii xs).
    {
      intros i Hi.
      specialize (Hascii (i + 1)).
      rewrite Znth_cons in Hascii by lia.
      replace (i + 1 - 1) with i in Hascii by lia.
      apply Hascii.
      rewrite Zlength_cons. lia.
    }
    rewrite ascii_eqb_ascii_of_z_const_125 by assumption.
    subst c.
    destruct (Z.eqb_spec x (Z.of_nat n)); [discriminate|].
    apply IH with (c := Z.of_nat n); auto.
Qed.

Lemma odd_lower_count_payload_125_app_single : forall s c,
  odd_lower_count_payload_125 (s ++ [c]) =
  odd_lower_count_payload_125 s + (if is_odd_lower_z_125 c then 1 else 0).
Proof.
  induction s as [|x xs IH]; intros c; simpl.
  - lia.
  - rewrite IH.
    destruct (is_odd_lower_z_125 x);
      destruct (is_odd_lower_z_125 c); lia.
Qed.

Lemma odd_lower_prefix_125_step_hit : forall s i,
  0 <= i < Zlength s ->
  97 <= Znth i (c_string s) 0 ->
  Znth i (c_string s) 0 <= 122 ->
  Z.rem (Znth i (c_string s) 0) 2 = 0 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i + 1.
Proof.
  intros s i Hi Hlo Hhi Hrem.
  unfold odd_lower_prefix_125.
  rewrite (sublist_split 0 (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0]
    by (symmetry; apply sublist_single; lia).
  rewrite odd_lower_count_payload_125_app_single.
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo, Hhi, Hrem by lia.
  replace (Z.leb 97 (Znth i s 0)) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i s 0) 122) with true
    by (symmetry; apply Z.leb_le; lia).
  rewrite Hrem, Z.eqb_refl.
  simpl.
  lia.
Qed.

Lemma odd_lower_prefix_125_step_skip : forall s i,
  0 <= i < Zlength s ->
  is_odd_lower_z_125 (Znth i s 0) = false ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hskip.
  unfold odd_lower_prefix_125.
  rewrite (sublist_split 0 (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0]
    by (symmetry; apply sublist_single; lia).
  rewrite odd_lower_count_payload_125_app_single.
  rewrite Hskip.
  lia.
Qed.

Lemma odd_lower_prefix_125_step_high : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 > 122 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hhi.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hhi by lia.
  replace (Z.leb (Znth i s 0) 122) with false
    by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.leb 97 (Znth i s 0)); reflexivity.
Qed.

Lemma odd_lower_prefix_125_step_low : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 < 97 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hlo.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo by lia.
  replace (Z.leb 97 (Znth i s 0)) with false
    by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma odd_lower_prefix_125_step_rem_nonzero : forall s i,
  0 <= i < Zlength s ->
  97 <= Znth i (c_string s) 0 ->
  Znth i (c_string s) 0 <= 122 ->
  Z.rem (Znth i (c_string s) 0) 2 <> 0 ->
  odd_lower_prefix_125 s (i + 1) = odd_lower_prefix_125 s i.
Proof.
  intros s i Hi Hlo Hhi Hrem.
  apply odd_lower_prefix_125_step_skip; [exact Hi|].
  unfold is_odd_lower_z_125.
  rewrite c_string_Znth_before_125 in Hlo, Hhi, Hrem by lia.
  replace (Z.leb 97 (Znth i s 0)) with true
    by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (Znth i s 0) 122) with true
    by (symmetry; apply Z.leb_le; lia).
  destruct (Z.eqb_spec (Z.rem (Znth i s 0) 2) 0); [contradiction|].
  reflexivity.
Qed.

Lemma odd_lower_prefix_125_final : forall s i,
  i = Zlength s ->
  odd_lower_prefix_125 s i = odd_lower_count_125 s.
Proof.
  intros s i Hi.
  subst i.
  unfold odd_lower_prefix_125, odd_lower_count_125.
  rewrite (sublist_self s (Zlength s) eq_refl).
  reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac c125_entailer :=
  constructor; pre_process_default; entailer!; try lia.

Ltac solve_rem10_bound :=
  match goal with
  | H : 0 <= ?tmp |- context[?tmp % 10] =>
      pose proof (Z.rem_bound_pos tmp 10 ltac:(lia) ltac:(lia)); lia
  end.

Ltac solve_contains_zb_125 :=
  match goal with
  | Hres : strchr_result ?s ?c ?ret ?p,
    Hnz : ?ret <> 0
    |- contains_zb_125 ?s ?c = true =>
      eapply strchr_result_nonzero_contains_zb_125;
      [lia | exact Hnz | exact Hres]
  | Hres : strchr_result ?s ?c ?ret ?p,
    Hz : ?ret = 0
    |- contains_zb_125 ?s ?c = false =>
      subst ret;
      eapply strchr_result_zero_contains_zb_125;
      [lia | exact Hres]
  end.

Ltac split_words_entailer_125 :=
  unfold store_string;
  entailer!;
  try solve [assumption | solve_contains_zb_125 | lia].

Ltac split_words_scan_init_125 :=
  Exists (@nil Z) (@nil (list Z));
  repeat match goal with
  | H : ?x = _ |- _ => subst x
  end;
  unfold split_scan_state_125, split_completed_rows_125,
    split_completed_payloads_125, split_scan_current_125,
    split_words_rows_heap_125;
  simpl;
  rewrite ?PtrArray.seg_empty;
  match goal with
  | |- ?P |-- _ =>
      match P with
      | context [PtrArray.undef_full ?p ?m] =>
          sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg p m)
      end
  end;
  entailer!;
  try solve [
    assumption
  | lia
  | apply string_length_nonneg
  | match goal with
    | s : list Z |- _ =>
        pose proof (string_length_nonneg s);
        lia
    end
  ].

Lemma c125_orp_intros_4_2 : forall A B C D,
  B |-- A || B || C || D.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - eapply derivable1_trans.
    + apply derivable1_orp_intros1.
    + apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_4_3 : forall A B C D,
  C |-- A || B || C || D.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_2 : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_3 : forall A B C,
  C |-- A || B || C.
Proof.
  intros.
  apply derivable1_orp_intros2.
Qed.

Lemma c125_orp_intros_3_mid : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma c125_orp_intros_3_second : forall A B C,
  B |-- A || B || C.
Proof.
  intros.
  eapply derivable1_trans.
  - apply derivable1_orp_intros2.
  - apply derivable1_orp_intros1.
Qed.

Lemma char_undef_missing_i_tail_pos_125 : forall x pos,
  0 <= pos ->
  CharArray.undef_missing_i x pos 0 (pos + 1) |--
  CharArray.undef_seg x 0 pos.
Proof.
  intros.
  replace (CharArray.undef_missing_i x pos 0 (pos + 1))
    with (CharArray.undef_missing_i x (pos + 1 - 1) 0 (pos + 1))
    by (f_equal; lia).
  replace (CharArray.undef_seg x 0 pos)
    with (CharArray.undef_seg x 0 (pos + 1 - 1))
    by (f_equal; lia).
  apply CharArray.undef_missing_i_to_undef_seg_tail.
  lia.
Qed.

Lemma char_full_cons_merge_125 : forall buf pos len v done,
  0 <= len ->
  (buf + pos * sizeof(CHAR)) # Char |-> v **
  CharArray.full (buf + (pos + 1) * sizeof(CHAR)) len done
  |-- CharArray.full (buf + pos * sizeof(CHAR)) (len + 1) (v :: done).
Proof.
  intros.
  sep_apply_l_atomic (CharArray.seg_single buf pos v).
  sep_apply_l_atomic (CharArray.seg_to_full buf pos (pos + 1) (v :: nil)).
  replace (pos + 1 - pos) with 1 by lia.
  replace (buf + (pos + 1) * sizeof(CHAR))
    with (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) by lia.
  replace (CharArray.full (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) len done)
    with (CharArray.full (buf + pos * sizeof(CHAR) + 1 * sizeof(CHAR)) (len + 1 - 1) done)
    by (f_equal; lia).
  sep_apply_l_atomic (CharArray.full_merge_to_full
    (buf + pos * sizeof(CHAR)) 1 (len + 1) (v :: nil) done ltac:(lia)).
  simpl.
  cancel.
Qed.

Lemma char_full_snoc_zero_125 : forall buf len done,
  Zlength done = len ->
  CharArray.full buf len done **
  (buf + len * sizeof(CHAR)) # Char |-> 0
  |-- CharArray.full buf (len + 1) (c_string done).
Proof.
  intros buf len done Hlen.
  unfold c_string.
  apply helper_chararray_full_snoc.
  rewrite <- Hlen.
  apply Zlength_nonneg.
Qed.

Lemma word_payload_125_empty_manual : forall s start,
  word_payload_125 s start start = @nil Z.
Proof.
  intros s start.
  unfold word_payload_125.
  apply sublist_nil.
  lia.
Qed.


Lemma proof_of_write_decimal_safety_wit_4 : write_decimal_safety_wit_4.
Proof.
  c125_entailer; solve_rem10_bound.
Qed.


Lemma proof_of_write_decimal_entail_wit_1 : write_decimal_entail_wit_1.
Proof.
  right.
  pre_process_default.
  entailer!.
  - sep_apply_l_atomic
      (CharArray.undef_full_split_to_undef_seg buf_pre digits_pre (digits_pre + 1)
         ltac:(lia)).
    sep_apply_l_atomic (CharArray.undef_seg_to_undef_full buf_pre 0 digits_pre).
    replace (buf_pre + 0 * sizeof(CHAR)) with buf_pre by lia.
    replace (digits_pre - 0) with (digits_pre - 1 + 1) by lia.
    cancel.
  - unfold decimal_write_state_125.
    split; [lia | rewrite Zlength_nil; lia].
Qed.

Lemma proof_of_write_decimal_entail_wit_2 : write_decimal_entail_wit_2.
Proof.
  left.
  pre_process_default.
  Exists (signed_last_nbits (48 + tmp % 10) 8 :: done_2).
  entailer!.
  - sep_apply_l_atomic (char_undef_missing_i_tail_pos_125 buf_pre pos ltac:(lia)).
    replace (pos - 1 + 1) with pos by lia.
    replace (digits_pre - (pos - 1) - 1) with ((digits_pre - pos - 1) + 1) by lia.
    sep_apply_l_atomic (char_full_cons_merge_125
      buf_pre pos (digits_pre - pos - 1) (signed_last_nbits (48 + tmp % 10) 8) done_2
      ltac:(lia)).
    cancel.
  - unfold decimal_write_state_125 in *.
    destruct PreH9 as [? ?].
    split; [lia | rewrite Zlength_cons; lia].
  - apply Z.quot_le_upper_bound; lia.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_write_decimal_return_wit_1 : write_decimal_return_wit_1.
Proof.
  left.
  pre_process_default.
  Exists done.
  entailer!.
  - unfold decimal_write_state_125 in PreH9.
    destruct PreH9 as [? Hlen].
    replace pos with (-1) in * by lia.
    replace (-1 + 1) with 0 by lia.
    replace (digits_pre - -1 - 1) with digits_pre by lia.
    replace (buf_pre + 0 * sizeof(CHAR)) with buf_pre by lia.
    assert (Hdone_len : Zlength done = digits_pre).
    { replace digits_pre with (digits_pre - -1 - 1) by lia.
      exact Hlen. }
    sep_apply (char_full_snoc_zero_125 buf_pre digits_pre done Hdone_len).
    rewrite (CharArray.undef_seg_empty buf_pre (digits_pre + 1)).
    entailer!.
  - unfold decimal_write_state_125 in PreH9.
    destruct PreH9 as [? Hlen].
    replace pos with (-1) in * by lia.
    lia.
Qed.

Lemma proof_of_split_words_entail_wit_1_1 : split_words_entail_wit_1_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply derivable1_orp_intros2.
  split_words_entailer_125.
Qed.

Lemma proof_of_split_words_entail_wit_1_2 : split_words_entail_wit_1_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply derivable1_orp_intros1.
  split_words_entailer_125.
Qed.

Lemma proof_of_split_words_entail_wit_2_1 : split_words_entail_wit_2_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  split_words_scan_init_125.
Qed.

Lemma proof_of_split_words_entail_wit_2_2 : split_words_entail_wit_2_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  split_words_scan_init_125.
Qed.

Lemma proof_of_split_words_entail_wit_3_1 : split_words_entail_wit_3_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold split_scan_state_125 in PreH30.
  destruct PreH30 as [Hscan_range [Hscan_rows Hscan_cur]].
  destruct Hscan_cur as [[Hcur_empty Hstart_neg] | [Hstart_range Hcur_payload]];
    [lia |].
  unfold store_string.
  entailer!;
  try solve [assumption | lia | exact Hcur_payload].
  - unfold word_payload_125.
    unfold string_length in *.
    rewrite Zlength_sublist by lia.
    lia.
  - unfold split_scan_state_125.
    repeat split; try lia; auto.
Qed.

Lemma proof_of_split_words_entail_wit_3_2 : split_words_entail_wit_3_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold split_scan_state_125 in PreH29.
  destruct PreH29 as [Hscan_range [Hscan_rows Hscan_cur]].
  destruct Hscan_cur as [[Hcur_empty Hstart_neg] | [Hstart_range Hcur_payload]];
    [lia |].
  unfold store_string.
  entailer!;
  try solve [assumption | lia | exact Hcur_payload].
  - unfold word_payload_125.
    unfold string_length in *.
    rewrite Zlength_sublist by lia.
    lia.
  - unfold split_scan_state_125.
    repeat split; try lia; auto.
Qed.

Lemma proof_of_split_words_entail_wit_4_1 : split_words_entail_wit_4_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_4_2 : split_words_entail_wit_4_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_5_1 : split_words_entail_wit_5_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  replace k with len in * by lia.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_125 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_125 str_l start i) = len + 1).
  {
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  rewrite <- word_row_125_unfold.
  replace (word_row_125 str_l start (start + len))
    with (word_row_125 str_l start i) by (f_equal; lia).
  replace (len + 1) with (Zlength (word_row_125 str_l start i)) by lia.
  sep_apply (split_words_rows_heap_125_app_single
    output_ptrs_2 output_rows_2 w (word_row_125 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!;
  try solve [assumption | lia | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  apply split_scan_state_125_step_delim_nonempty.
  - assumption.
  - lia.
  - rewrite PreH17 in PreH18.
    rewrite c_string_Znth_before_125 in PreH18 by (unfold string_length in *; lia).
    exact PreH18.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_5_2 : split_words_entail_wit_5_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace k with len in * by lia.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_125 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_125 str_l start i) = len + 1).
  {
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  rewrite <- word_row_125_unfold.
  replace (word_row_125 str_l start (start + len))
    with (word_row_125 str_l start i) by (f_equal; lia).
  replace (len + 1) with (Zlength (word_row_125 str_l start i)) by lia.
  sep_apply (split_words_rows_heap_125_app_single
    output_ptrs_2 output_rows_2 w (word_row_125 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!;
  try solve [assumption | lia | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia].
  apply split_scan_state_125_step_delim_nonempty.
  - assumption.
  - lia.
  - rewrite PreH17 in PreH18.
    rewrite c_string_Znth_before_125 in PreH18 by (unfold string_length in *; lia).
    exact PreH18.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_6_1 : split_words_entail_wit_6_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_delim_empty.
  - exact PreH27.
  - rewrite <- c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_6_2 : split_words_entail_wit_6_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_delim_empty.
  - exact PreH28.
  - rewrite <- c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_1 : split_words_entail_wit_7_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH23 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_nondelim_continue.
  - exact PreH27.
  - lia.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_2 : split_words_entail_wit_7_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH24 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_nondelim_continue.
  - exact PreH28.
  - lia.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_3 : split_words_entail_wit_7_3.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH23 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH27].
  apply split_scan_state_125_step_nondelim_start.
  - exact PreH27.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_7_4 : split_words_entail_wit_7_4.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace start with (-1) in * by lia.
  Exists output_ptrs_2 output_rows_2.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125; [exact PreH24 | unfold string_length in *; lia]).
  unfold store_string.
  entailer!;
  try solve [lia | exact PreH28].
  apply split_scan_state_125_step_nondelim_start.
  - exact PreH28.
  - intro Hbad.
    apply PreH2.
    rewrite c_string_Znth_before_125 by (unfold string_length in *; lia).
    exact Hbad.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_split_words_entail_wit_9_1 : split_words_entail_wit_9_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  - apply Zlength_word_payload_125; unfold string_length in *; lia.
  - unfold split_scan_state_125 in PreH29.
    destruct PreH29 as [Hrange [Hrows Hcur]].
    destruct Hcur as [[Hempty Hbad] | [Hstart Hcur]];
      [lia | exact Hcur].
Qed.

Lemma proof_of_split_words_entail_wit_9_2 : split_words_entail_wit_9_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_125 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia;
        symmetry; apply word_payload_125_empty_manual).
  rewrite CharArray.full_empty.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  - apply Zlength_word_payload_125; unfold string_length in *; lia.
  - unfold split_scan_state_125 in PreH28.
    destruct PreH28 as [Hrange [Hrows Hcur]].
    destruct Hcur as [[Hempty Hbad] | [Hstart Hcur]];
      [lia | exact Hcur].
Qed.

Lemma proof_of_split_words_entail_wit_10_1 : split_words_entail_wit_10_1.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_10_2 : split_words_entail_wit_10_2.
Proof.
  pre_process_default.
  eapply derivable1_trans.
  2: apply c125_orp_intros_3_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | lia].
  rewrite word_payload_125_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_split_words_entail_wit_11_1 : split_words_entail_wit_11_1.
Proof.
  pre_process_default.
  assert (Hi : i = n) by lia.
  assert (Hs : start = -1) by lia.
  subst i start.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | apply problem_125_spec_z_any | lia].
  unfold string_length in *.
  rewrite PreH5 in PreH26.
  apply split_scan_state_125_final_empty.
  exact PreH26.
Qed.

Lemma proof_of_split_words_entail_wit_11_2 : split_words_entail_wit_11_2.
Proof.
  pre_process_default.
  assert (Hi : i = n) by lia.
  assert (Hs : start = -1) by lia.
  subst i start.
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!;
  try solve [assumption | apply problem_125_spec_z_any | lia].
  unfold string_length in *.
  rewrite PreH5 in PreH27.
  apply split_scan_state_125_final_empty.
  exact PreH27.
Qed.

Lemma proof_of_split_words_entail_wit_11_3 : split_words_entail_wit_11_3.
Proof.
  pre_process_default.
  assert (Hk : k = len) by lia.
  subst k.
  assert (Hstop : start + len = n) by lia.
  replace (word_payload_125 str_l start (start + len) ++ 0 :: nil)
    with (word_row_125 str_l start n).
  2:{
    rewrite Hstop.
    unfold word_row_125, c_string.
    reflexivity.
  }
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_2.
  Exists (output_ptrs_2 ++ cons w nil)
    (output_rows_2 ++ cons (word_row_125 str_l start n) nil).
  replace (len + 1) with (Zlength (word_row_125 str_l start n)).
  2:{
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  sep_apply (split_words_rows_heap_125_app_single output_ptrs_2 output_rows_2 w
    (word_row_125 str_l start n) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite Zlength_app, !Zlength_cons, !Zlength_nil; lia
  ].
  unfold string_length in *.
  rewrite PreH4 in PreH27.
  rewrite PreH4.
  apply split_scan_state_125_final_nonempty; try lia.
  exact PreH27.
Qed.

Lemma proof_of_split_words_entail_wit_11_4 : split_words_entail_wit_11_4.
Proof.
  pre_process_default.
  assert (Hk : k = len) by lia.
  subst k.
  assert (Hstop : start + len = n) by lia.
  replace (word_payload_125 str_l start (start + len) ++ 0 :: nil)
    with (word_row_125 str_l start n).
  2:{
    rewrite Hstop.
    unfold word_row_125, c_string.
    reflexivity.
  }
  eapply derivable1_trans.
  2: apply c125_orp_intros_4_3.
  Exists (output_ptrs_2 ++ cons w nil)
    (output_rows_2 ++ cons (word_row_125 str_l start n) nil).
  replace (len + 1) with (Zlength (word_row_125 str_l start n)).
  2:{
    rewrite word_row_125_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_125 by (unfold string_length in *; lia).
    lia.
  }
  sep_apply (split_words_rows_heap_125_app_single output_ptrs_2 output_rows_2 w
    (word_row_125 str_l start n) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite Zlength_app, !Zlength_cons, !Zlength_nil; lia
  ].
  unfold string_length in *.
  rewrite PreH4 in PreH28.
  rewrite PreH4.
  apply split_scan_state_125_final_nonempty; try lia.
  exact PreH28.
Qed.





Lemma proof_of_split_words_entail_wit_12 : split_words_entail_wit_12.
Proof.
  left.
  pre_process_default.
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | solve_contains_zb_125
  | unfold odd_lower_prefix_125, odd_lower_count_125;
    rewrite sublist_nil by lia; reflexivity
  | pose proof (string_length_nonneg str_l); lia
  ].
Qed.


Lemma proof_of_split_words_entail_wit_13_1 : split_words_entail_wit_13_1.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH10.
  symmetry.
  apply odd_lower_prefix_125_step_hit.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    exact PreH1.
Qed.


Lemma proof_of_split_words_entail_wit_13_2 : split_words_entail_wit_13_2.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH9.
  symmetry.
  apply odd_lower_prefix_125_step_high.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
Qed.


Lemma proof_of_split_words_entail_wit_13_3 : split_words_entail_wit_13_3.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH8.
  symmetry.
  apply odd_lower_prefix_125_step_low.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
Qed.


Lemma proof_of_split_words_entail_wit_13_4 : split_words_entail_wit_13_4.
Proof.
  left.
  pre_process_default.
  assert (Hchar_range : 0 <= Znth i (c_string str_l) 0 <= 127)
    by (apply all_ascii_c_string_Znth_125;
        [match goal with H : all_ascii str_l |- _ => exact H end
        | unfold string_length in *; lia]).
  entailer!;
  try solve [assumption | lia].
  rewrite PreH10.
  symmetry.
  apply odd_lower_prefix_125_step_rem_nonzero.
  - unfold string_length in *; lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    lia.
  - change (naive_C_Rules.c_string str_l) with (c_string str_l).
    exact PreH1.
Qed.

Lemma proof_of_split_words_entail_wit_14 : split_words_entail_wit_14.
Proof.
  left.
  pre_process_default.
  Exists (cons retval_2 nil) out_l.
  sep_apply_l_atomic (PtrArray.seg_single data 0 retval_2).
  sep_apply_l_atomic (PtrArray.undef_missing_i_to_undef_seg_head data 0 (n + 1) ltac:(lia)).
  unfold store_string.
  entailer!;
  try solve [
    assumption
  | apply problem_125_spec_z_any
  | rewrite !Zlength_cons, !Zlength_nil; lia
  ].
  - replace (0 + 1) with 1 by lia.
    simpl.
    replace (Zlength (c_string out_l)) with (retval + 1) by (
      unfold c_string, string_length;
      rewrite Zlength_app, Zlength_cons, Zlength_nil;
      lia
    ).
    cancel.
    entailer!.
  - unfold string_length in *.
    rewrite PreH13.
    apply odd_lower_prefix_125_final.
    lia.
Qed.

Lemma proof_of_split_words_return_wit_1 : split_words_return_wit_1.
Proof.
  left.
  pre_process_default.
  subst output_ptrs_2 n.
  Exists (cons (c_string digit_l) nil) (cons w nil) data_2.
  rewrite !Zlength_cons, !Zlength_nil.
  entailer!;
  try solve [assumption | pose proof (string_length_nonneg str_l); lia].
Qed.

Lemma proof_of_split_words_return_wit_3 : split_words_return_wit_3.
Proof.
  left.
  pre_process_default.
  subst n.
  rewrite PreH8.
  Exists output_rows_2 output_ptrs_2 data_2.
  entailer!;
  try solve [
    assumption
  | pose proof (string_length_nonneg str_l); lia
  | subst output_rows_2; apply Zlength_split_output_rows_125_le
  | match goal with
    | H : output_rows_2 = split_output_rows_125 str_l _ |- _ =>
        rewrite H; apply Zlength_split_output_rows_125_le
    end].
Qed.

Lemma proof_of_split_words_return_wit_4 : split_words_return_wit_4.
Proof.
  left.
  pre_process_default.
  subst n.
  rewrite PreH8.
  Exists output_rows_2 output_ptrs_2 data_2.
  entailer!;
  try solve [
    assumption
  | pose proof (string_length_nonneg str_l); lia
  | subst output_rows_2; apply Zlength_split_output_rows_125_le
  | match goal with
    | H : output_rows_2 = split_output_rows_125 str_l _ |- _ =>
        rewrite H; apply Zlength_split_output_rows_125_le
    end].
Qed.
