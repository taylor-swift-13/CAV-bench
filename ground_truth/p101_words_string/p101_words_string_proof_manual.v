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
From SimpleC.EE.CAV.ground_truth_p101_words_string Require Import p101_words_string_goal.
From SimpleC.EE.CAV.ground_truth_p101_words_string Require Import p101_words_string_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p101_words_string.
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



Lemma words_rows_heap_101_nil :
  emp |-- words_rows_heap_101 nil nil.
Proof.
  simpl.
  entailer!.
Qed.

Lemma words_rows_heap_101_app_single : forall ptrs rows p row,
  Zlength ptrs = Zlength rows ->
  words_rows_heap_101 ptrs rows ** CharArray.full p (Zlength row) row
  |-- words_rows_heap_101 (ptrs ++ [p]) (rows ++ [row]).
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

Lemma String_length_string_of_list_z_101 : forall l,
  String.length (string_of_list_z_101 l) = List.length l.
Proof.
  induction l as [| x xs IH]; simpl; congruence.
Qed.

Lemma row_payload_c_string_101 : forall payload,
  row_payload_z_101 (c_string payload) = payload.
Proof.
  intros payload.
  unfold row_payload_z_101, c_string.
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

Lemma rows_to_strings_c_string_101 : forall payloads,
  rows_to_strings_z_101 (map c_string payloads) =
  map string_of_list_z_101 payloads.
Proof.
  induction payloads as [| p ps IH]; simpl; [reflexivity|].
  unfold row_string_z_101.
  rewrite row_payload_c_string_101.
  rewrite IH.
  reflexivity.
Qed.

Lemma Zlength_map_101 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros.
  repeat rewrite Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma ascii_of_z_101_nat_of_ascii : forall z,
  0 <= z < 128 ->
  nat_of_ascii (ascii_of_z_101 z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of_z_101.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma string_of_list_ascii_map_ascii_of_z_101 : forall s,
  string_of_list_ascii (map ascii_of_z_101 s) = string_of_list_z_101 s.
Proof.
  induction s as [| c cs IH]; simpl; congruence.
Qed.

Lemma list_ascii_of_string_of_list_z_101 : forall s,
  list_ascii_of_string (string_of_list_z_101 s) =
  map ascii_of_z_101 s.
Proof.
  induction s as [| c cs IH]; simpl; congruence.
Qed.

Lemma is_delimiter_code_101 : forall c,
  is_delimiter c =
  (Nat.eqb (nat_of_ascii c) 44 || Nat.eqb (nat_of_ascii c) 32)%bool.
Proof.
  intros [[] [] [] [] [] [] [] []]; reflexivity.
Qed.

Lemma Nat_eqb_Z_to_nat_101 : forall z k,
  0 <= z ->
  0 <= k ->
  (Nat.eqb (Z.to_nat z) (Z.to_nat k)) = Z.eqb z k.
Proof.
  intros z k Hz Hk.
  destruct (Z.eqb_spec z k) as [Heq | Hneq].
  - subst. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq.
    intro Hnat.
    apply Hneq.
    apply Z2Nat.inj in Hnat; lia.
Qed.

Lemma is_delimiter_ascii_of_z_101 : forall z,
  0 <= z < 128 ->
  is_delimiter (ascii_of_z_101 z) = is_delim_z_101 z.
Proof.
  intros z Hz.
  rewrite is_delimiter_code_101.
  rewrite ascii_of_z_101_nat_of_ascii by lia.
  unfold is_delim_z_101.
  change 44%nat with (Z.to_nat 44).
  change 32%nat with (Z.to_nat 32).
  rewrite !Nat_eqb_Z_to_nat_101 by lia.
  rewrite Bool.orb_comm.
  reflexivity.
Qed.

Lemma nth_map_ascii_Znth_101 : forall s n,
  (n < List.length s)%nat ->
  nth n (map ascii_of_z_101 s) "000"%char =
  ascii_of_z_101 (Znth (Z.of_nat n) s 0).
Proof.
  induction s as [| x xs IH]; intros [| n] Hlt; simpl in *; try lia.
  - reflexivity.
  - rewrite Znth_cons by lia.
    replace (Z.pos (Pos.of_succ_nat n) - 1) with (Z.of_nat n) by lia.
    apply IH. lia.
Qed.

Lemma split_step_ascii_map_101 : forall st c,
  0 <= c < 128 ->
  split_step_ascii_101 (map_state_ascii_101 st) (ascii_of_z_101 c) =
  map_state_ascii_101 (split_step_101 st c).
Proof.
  intros [rows cur] c Hc.
  unfold split_step_ascii_101, map_state_ascii_101, split_step_101; simpl.
  rewrite is_delimiter_ascii_of_z_101 by lia.
  destruct (is_delim_z_101 c); destruct cur as [| x xs]; simpl;
    rewrite ?map_app; reflexivity.
Qed.

Lemma split_state_nat_ascii_map_101 : forall n s,
  (n <= List.length s)%nat ->
  all_ascii s ->
  split_state_nat_ascii_101 n (map ascii_of_z_101 s) =
  map_state_ascii_101 (split_state_nat_101 n s).
Proof.
  induction n as [| n IH]; intros s Hlen Hascii; simpl.
  - reflexivity.
  - rewrite IH by (try exact Hascii; lia).
    rewrite nth_map_ascii_Znth_101 by lia.
    rewrite split_step_ascii_map_101.
    + reflexivity.
    + pose proof (Hascii (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)).
      lia.
Qed.

Lemma split_state_nat_ascii_step_101 : forall s n,
  (n < List.length s)%nat ->
  split_state_nat_ascii_101 (S n) s =
  split_step_ascii_101 (split_state_nat_ascii_101 n s) (nth n s "000"%char).
Proof.
  reflexivity.
Qed.

Lemma skipn_nth_cons_101 : forall {A : Type} (s : list A) n d,
  (n < List.length s)%nat ->
  skipn n s = nth n s d :: skipn (S n) s.
Proof.
  induction s as [| x xs IH]; intros [| n] d Hlen; simpl in *; try lia.
  - reflexivity.
  - apply IH. lia.
Qed.

Lemma words_string_aux_split_state_nat_ascii_101 : forall s n rows cur,
  (n <= List.length s)%nat ->
  split_state_nat_ascii_101 n s = (rows, cur) ->
  words_string_aux [] s = rows ++ words_string_aux cur (skipn n s).
Proof.
  induction n as [| n IH]; intros rows cur Hlen Hst.
  - simpl in Hst. inversion Hst; subst. reflexivity.
  - assert (Hnlen : (n < List.length s)%nat) by lia.
    destruct (split_state_nat_ascii_101 n s) as [rows0 cur0] eqn:Hprev.
    specialize (IH rows0 cur0 ltac:(lia) eq_refl).
    rewrite IH.
    rewrite (skipn_nth_cons_101 s n "000"%char) by lia.
    simpl in Hst.
    rewrite Hprev in Hst.
    unfold split_step_ascii_101 in Hst.
    destruct (is_delimiter (nth n s "000"%char)) eqn:Hdelim.
    + destruct cur0 as [| c cs].
      * inversion Hst; subst.
        simpl. rewrite Hdelim. reflexivity.
      * inversion Hst; subst.
        simpl. rewrite Hdelim. rewrite <- app_assoc. reflexivity.
    + inversion Hst; subst.
      simpl. rewrite Hdelim. reflexivity.
Qed.

Lemma words_string_list_impl_split_state_nat_ascii_101 : forall s,
  words_string_list_impl s =
  let '(rows, cur) := split_state_nat_ascii_101 (List.length s) s in
  match cur with
  | [] => rows
  | _ => rows ++ [cur]
  end.
Proof.
  intros s.
  unfold words_string_list_impl.
  destruct (split_state_nat_ascii_101 (List.length s) s) as [rows cur] eqn:Hst.
  rewrite (words_string_aux_split_state_nat_ascii_101 s (List.length s) rows cur)
    by (try exact Hst; lia).
  rewrite skipn_all.
  destruct cur; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma map_ascii_words_payloads_101 : forall s,
  all_ascii s ->
  words_string_list_impl (map ascii_of_z_101 s) =
  map (map ascii_of_z_101) (words_payloads_101 s).
Proof.
  intros s Hascii.
  rewrite words_string_list_impl_split_state_nat_ascii_101.
  rewrite length_map.
  rewrite split_state_nat_ascii_map_101.
  - unfold words_payloads_101, map_state_ascii_101.
    rewrite Zlength_correct, Nat2Z.id.
    destruct (split_state_nat_101 (List.length s) s) as [rows cur].
    simpl.
    destruct cur; rewrite ?map_app; reflexivity.
  - lia.
  - exact Hascii.
Qed.

Lemma problem_101_spec_z_words_output_rows_101 : forall s,
  all_ascii s ->
  problem_101_spec_z s (words_output_rows_101 s).
Proof.
  intros s Hascii.
  unfold problem_101_spec_z, problem_101_spec, words_string,
    words_output_rows_101.
  rewrite rows_to_strings_c_string_101.
  rewrite list_ascii_of_string_of_list_z_101.
  rewrite map_ascii_words_payloads_101 by exact Hascii.
  rewrite map_map.
  apply map_ext.
  intro row.
  rewrite string_of_list_ascii_map_ascii_of_z_101.
  reflexivity.
Qed.

Lemma split_state_nat_101_rows_bound : forall n s rows cur,
  split_state_nat_101 n s = (rows, cur) ->
  Zlength rows <= Z.of_nat n.
Proof.
  induction n as [| n IH]; intros s rows cur Hst; simpl in Hst.
  - inversion Hst; subst. rewrite Zlength_nil. lia.
  - destruct (split_state_nat_101 n s) as [rows0 cur0] eqn:Hprev.
    unfold split_step_101 in Hst.
    destruct (is_delim_z_101 (Znth (Z.of_nat n) s 0)).
    + destruct cur0 as [| c cs]; inversion Hst; subst.
      * specialize (IH s rows [] Hprev). lia.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil.
        specialize (IH s rows0 (c :: cs) Hprev). lia.
    + inversion Hst; subst.
      specialize (IH s rows cur0 Hprev).
      lia.
Qed.

Lemma Zlength_words_output_rows_101_le : forall s,
  Zlength (words_output_rows_101 s) <= Zlength s + 1.
Proof.
  intros s.
  unfold words_output_rows_101, words_payloads_101.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [rows cur] eqn:Hst.
  destruct cur as [| c cs].
  - rewrite Zlength_map_101.
    pose proof (split_state_nat_101_rows_bound _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
  - rewrite Zlength_map_101, Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (split_state_nat_101_rows_bound _ _ _ _ Hst).
    rewrite Z2Nat.id in H by (pose proof (Zlength_nonneg s); lia).
    lia.
Qed.

Lemma split_state_nat_101_step : forall i s,
  0 <= i ->
  split_state_nat_101 (Z.to_nat (i + 1)) s =
  split_step_101 (split_state_nat_101 (Z.to_nat i) s) (Znth i s 0).
Proof.
  intros i s Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_cons : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = true ->
  cur <> [] ->
  split_completed_rows_101 s (i + 1) =
  map c_string rows ++ [c_string cur].
Proof.
  intros s i rows cur Hi Hst Hdelim Hcur.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  destruct cur; [contradiction|].
  simpl.
  rewrite map_app.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_empty : forall s i rows,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, []) ->
  is_delim_z_101 (Znth i s 0) = true ->
  split_completed_rows_101 s (i + 1) = map c_string rows.
Proof.
  intros s i rows Hi Hst Hdelim.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_completed_rows_101_step_nondelim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = false ->
  split_completed_rows_101 s (i + 1) = map c_string rows.
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_completed_rows_101, split_completed_payloads_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_scan_current_101_step_nondelim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = false ->
  split_scan_current_101 s (i + 1) = cur ++ [Znth i s 0].
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_scan_current_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  reflexivity.
Qed.

Lemma split_scan_current_101_step_delim : forall s i rows cur,
  0 <= i ->
  split_state_nat_101 (Z.to_nat i) s = (rows, cur) ->
  is_delim_z_101 (Znth i s 0) = true ->
  split_scan_current_101 s (i + 1) = [].
Proof.
  intros s i rows cur Hi Hst Hdelim.
  unfold split_scan_current_101.
  rewrite split_state_nat_101_step by lia.
  rewrite Hst.
  unfold split_step_101.
  rewrite Hdelim.
  destruct cur; reflexivity.
Qed.

Lemma word_payload_101_step : forall s start i,
  0 <= start /\ start <= i /\ i < Zlength s ->
  word_payload_101 s start (i + 1) =
  word_payload_101 s start i ++ [Znth i s 0].
Proof.
  intros s start i Hbounds.
  unfold word_payload_101.
  rewrite (sublist_split start (i + 1) i s) by lia.
  replace (sublist i (i + 1) s) with [Znth i s 0].
  - reflexivity.
  - symmetry.
    apply sublist_single.
    lia.
Qed.

Lemma c_string_Znth_before_101 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = Znth i s 0.
Proof.
  intros s i Hi.
  unfold c_string.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma Zlength_word_payload_101 : forall s start stop,
  0 <= start <= stop ->
  stop <= Zlength s ->
  Zlength (word_payload_101 s start stop) = stop - start.
Proof.
  intros s start stop Hbounds Hstop.
  unfold word_payload_101.
  rewrite Zlength_sublist by lia.
  lia.
Qed.

Lemma word_payload_101_empty : forall s start,
  word_payload_101 s start start = [].
Proof.
  intros s start.
  unfold word_payload_101.
  apply sublist_nil.
  lia.
Qed.

Lemma word_payload_101_step_offset_c_string : forall s start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength s ->
  word_payload_101 s start (start + (k + 1)) =
  word_payload_101 s start (start + k) ++
    [Znth (start + k) (c_string s) 0].
Proof.
  intros s start k Hstart Hk Hlt.
  replace (start + (k + 1)) with ((start + k) + 1) by lia.
  rewrite word_payload_101_step by lia.
  rewrite c_string_Znth_before_101 by lia.
  reflexivity.
Qed.

Lemma word_row_101_unfold : forall s start stop,
  word_row_101 s start stop =
  word_payload_101 s start stop ++ [0].
Proof.
  intros.
  unfold word_row_101, c_string.
  reflexivity.
Qed.

Lemma split_scan_state_101_initial : forall s,
  split_scan_state_101 s 0 (-1) [].
Proof.
  intros s.
  unfold split_scan_state_101, split_completed_rows_101,
    split_completed_payloads_101, split_scan_current_101, string_length.
  simpl.
  split; [rewrite Zlength_correct; lia|].
  split; [reflexivity|].
  left.
  split; reflexivity.
Qed.

Lemma is_delim_z_101_true_32 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = 32 ->
  is_delim_z_101 (Znth i s 0) = true.
Proof.
  intros s i Hi H.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma is_delim_z_101_true_44 : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 = 44 ->
  is_delim_z_101 (Znth i s 0) = true.
Proof.
  intros s i Hi H.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  rewrite H.
  reflexivity.
Qed.

Lemma is_delim_z_101_false_from_neq : forall s i,
  0 <= i < Zlength s ->
  Znth i (c_string s) 0 <> 32 ->
  Znth i (c_string s) 0 <> 44 ->
  is_delim_z_101 (Znth i s 0) = false.
Proof.
  intros s i Hi H32 H44.
  unfold is_delim_z_101.
  rewrite <- (c_string_Znth_before_101 s i) by lia.
  destruct (Z.eqb_spec (Znth i (c_string s) 0) 32); [congruence|].
  destruct (Z.eqb_spec (Znth i (c_string s) 0) 44); [congruence|].
  reflexivity.
Qed.

Lemma split_scan_state_101_current_nonempty : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  split_scan_current_101 s i = word_payload_101 s start i.
Proof.
  intros s i start rows Hstate Hstart.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [_ [[_ Hbad] | [_ Hcur]]]].
  - lia.
  - exact Hcur.
Qed.

Lemma split_scan_state_101_step_delim_nonempty : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  is_delim_z_101 (Znth i s 0) = true ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) (-1)
    (rows ++ [word_row_101 s start i]).
Proof.
  intros s i start rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart_bad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur as [| c cs].
    + simpl in Hcur.
      assert (Zlength (word_payload_101 s start i) = i - start).
      { apply Zlength_word_payload_101; lia. }
      rewrite <- Hcur in H.
      rewrite Zlength_nil in H.
      lia.
    + simpl.
      unfold word_row_101.
      rewrite map_app.
      rewrite Hcur.
      reflexivity.
  - left.
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; split; reflexivity.
Qed.

Lemma split_scan_state_101_step_delim_empty : forall s i rows,
  split_scan_state_101 s i (-1) rows ->
  is_delim_z_101 (Znth i s 0) = true ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) (-1) rows.
Proof.
  intros s i rows Hstate Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; [reflexivity|congruence].
  - left.
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur_empty.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_101.
    rewrite Hdelim.
    destruct cur; [split; reflexivity|congruence].
Qed.

Lemma split_scan_state_101_step_nondelim_continue : forall s i start rows,
  split_scan_state_101 s i start rows ->
  0 <= start < i ->
  is_delim_z_101 (Znth i s 0) = false ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) start rows.
Proof.
  intros s i start rows Hstate Hstart Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [Hstart2 Hcur]]; [lia|].
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    simpl in Hrows; subst rows.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur.
    unfold split_step_101.
    rewrite Hdelim.
    rewrite Hcur.
    rewrite word_payload_101_step by lia.
    reflexivity.
Qed.

Lemma split_scan_state_101_step_nondelim_start : forall s i rows,
  split_scan_state_101 s i (-1) rows ->
  is_delim_z_101 (Znth i s 0) = false ->
  i < Zlength s ->
  split_scan_state_101 s (i + 1) i rows.
Proof.
  intros s i rows Hstate Hdelim Hi.
  unfold split_scan_state_101 in *.
  destruct Hstate as [Hbounds [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur_empty Hstart] | [Hbad _]]; [|lia].
  subst.
  split; [unfold string_length in *; lia|].
  split.
  - unfold split_completed_rows_101, split_completed_payloads_101,
      split_scan_current_101 in *.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    rewrite split_state_nat_101_step by lia.
    rewrite Hst.
    unfold split_step_101.
    rewrite Hdelim.
    reflexivity.
  - right.
    split; [lia|].
    unfold split_scan_current_101.
    rewrite split_state_nat_101_step by lia.
    unfold split_scan_current_101 in Hcur_empty.
    destruct (split_state_nat_101 (Z.to_nat i) s) as [payloads cur] eqn:Hst.
    simpl in Hcur_empty.
    unfold split_step_101.
    rewrite Hdelim.
    subst cur.
    simpl.
    unfold word_payload_101.
    replace (sublist i (i + 1) s) with [Znth i s 0].
    + reflexivity.
    + symmetry; apply sublist_single; lia.
Qed.

Lemma split_scan_state_101_final_empty : forall s rows,
  split_scan_state_101 s (Zlength s) (-1) rows ->
  rows = words_output_rows_101 s.
Proof.
  intros s rows Hstate.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[Hcur Hstart] | [Hbad _]]; [| lia].
  subst rows.
  unfold words_output_rows_101, words_payloads_101,
    split_completed_rows_101, split_completed_payloads_101 in *.
  unfold split_scan_current_101 in Hcur.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [payloads cur].
  simpl in *.
  subst cur.
  reflexivity.
Qed.

Lemma split_scan_state_101_final_nonempty : forall s start rows,
  split_scan_state_101 s (Zlength s) start rows ->
  0 <= start < Zlength s ->
  rows ++ [word_row_101 s start (Zlength s)] = words_output_rows_101 s.
Proof.
  intros s start rows Hstate Hstart.
  unfold split_scan_state_101 in Hstate.
  destruct Hstate as [_ [Hrows Hcur_cases]].
  destruct Hcur_cases as [[_ Hbad] | [_ Hcur]]; [lia|].
  subst rows.
  unfold words_output_rows_101, words_payloads_101,
    split_completed_rows_101, split_completed_payloads_101 in *.
  unfold split_scan_current_101 in Hcur.
  destruct (split_state_nat_101 (Z.to_nat (Zlength s)) s) as [payloads cur].
  simpl in *.
  destruct cur as [| c cs].
  - assert (Zlength (word_payload_101 s start (Zlength s)) =
      Zlength s - start).
    { apply Zlength_word_payload_101; lia. }
    rewrite <- Hcur in H.
    rewrite Zlength_nil in H.
    lia.
  - unfold word_row_101.
    rewrite <- Hcur.
    simpl.
    rewrite map_app.
    reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_c_string_char_bound :=
  match goal with
  | Hvalid : valid_string ?s |- 0 <= Znth ?i (c_string ?s) 0 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  | Hvalid : valid_string ?s |- Znth ?i (c_string ?s) 0 <= 127 =>
      let Hbounds := fresh "Hbounds" in
      pose proof (c_string_char_bound s i Hvalid ltac:(lia)) as Hbounds; lia
  end.

Ltac solve_word_payload_goal :=
  match goal with
  | Hstate : split_scan_state_101 ?s ?i ?start ?rows
      |- split_scan_current_101 ?s ?i = word_payload_101 ?s ?start ?i =>
      apply (split_scan_state_101_current_nonempty s i start rows Hstate); lia
  | |- Zlength (word_payload_101 ?s ?start ?stop) = ?stop - ?start =>
      apply Zlength_word_payload_101; unfold string_length in *; lia
  end.

Ltac solve_delim_goal :=
  match goal with
  | H : Znth ?i (c_string ?s) 0 = 32
      |- is_delim_z_101 (Znth ?i (c_string ?s) 0) = true =>
      unfold is_delim_z_101; rewrite H; reflexivity
  | H : Znth ?i (c_string ?s) 0 = 44
      |- is_delim_z_101 (Znth ?i (c_string ?s) 0) = true =>
      unfold is_delim_z_101; rewrite H; reflexivity
  end.

Ltac words_entailer :=
  entailer!;
  try solve_c_string_char_bound;
  try solve_word_payload_goal;
  try solve_delim_goal;
  try lia.

Lemma proof_of_words_string_entail_wit_1 : words_string_entail_wit_1.
Proof.
  constructor.
  pre_process_default.
  Exists (@nil Z) (@nil (list Z)).
  sep_apply_l_atomic (PtrArray.undef_full_to_undef_seg retval_3 (retval + 1)).
  rewrite PtrArray.seg_empty.
  unfold store_string.
  entailer!.
  - apply split_scan_state_101_initial.
  - subst retval; apply string_length_nonneg.
Qed.

Lemma proof_of_words_string_entail_wit_2_1 : words_string_entail_wit_2_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_2_2 : words_string_entail_wit_2_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((i - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_3 : words_string_entail_wit_3.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  rewrite word_payload_101_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_4 : words_string_entail_wit_4.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  rewrite CharArray.undef_seg_empty.
  words_entailer.
  rewrite word_row_101_unfold.
  replace (start + k) with i by lia.
  replace (k + 1) with (len + 1) by lia.
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_5 : words_string_entail_wit_5.
Proof.
  constructor; pre_process_default.
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_101 str_l start i :: nil)).
  assert (Hrow_len : Zlength (word_row_101 str_l start i) = len + 1).
  {
    rewrite word_row_101_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_101 by (unfold string_length in *; lia).
    lia.
  }
  replace (len + 1) with (Zlength (word_row_101 str_l start i)) by lia.
  sep_apply (words_rows_heap_101_app_single
    output_ptrs_2 output_rows_2 w (word_row_101 str_l start i) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  words_entailer.
  apply split_scan_state_101_step_delim_nonempty.
  - exact PreH25.
  - lia.
  - rewrite PreH16 in PreH17.
    rewrite c_string_Znth_before_101 in PreH17 by (unfold string_length in *; lia).
    exact PreH17.
  - unfold string_length in *; lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_words_string_entail_wit_6_1 : words_string_entail_wit_6_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  replace start with (-1) by lia.
  apply split_scan_state_101_step_delim_empty.
  - replace start with (-1) in PreH25 by lia; exact PreH25.
  - apply is_delim_z_101_true_44; unfold string_length in *; lia || exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_6_2 : words_string_entail_wit_6_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  replace start with (-1) by lia.
  apply split_scan_state_101_step_delim_empty.
  - replace start with (-1) in PreH24 by lia; exact PreH24.
  - apply is_delim_z_101_true_32; unfold string_length in *; lia || exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_7_1 : words_string_entail_wit_7_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  apply split_scan_state_101_step_nondelim_continue.
  - exact PreH25.
  - lia.
  - apply is_delim_z_101_false_from_neq.
    + unfold string_length in *; lia.
    + exact PreH3.
    + exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_7_2 : words_string_entail_wit_7_2.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  apply split_scan_state_101_step_nondelim_start.
  - replace start with (-1) in PreH25 by lia; exact PreH25.
  - apply is_delim_z_101_false_from_neq.
    + unfold string_length in *; lia.
    + exact PreH3.
    + exact PreH2.
  - unfold string_length in *; lia.
Qed.

Lemma proof_of_words_string_entail_wit_9 : words_string_entail_wit_9.
Proof.
  constructor; pre_process_default.
  replace i with n in * by lia.
  Exists output_ptrs_2 output_rows_2.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg retval ((n - start) + 1)).
  replace (word_payload_101 str_l start (start + 0)) with (@nil Z)
    by (replace (start + 0) with start by lia; symmetry; apply word_payload_101_empty).
  rewrite CharArray.full_empty.
  unfold store_string; words_entailer.
Qed.

Lemma proof_of_words_string_entail_wit_10 : words_string_entail_wit_10.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2.
  unfold store_string; words_entailer.
  rewrite word_payload_101_step_offset_c_string by (unfold string_length in *; lia).
  reflexivity.
Qed.

Lemma proof_of_words_string_entail_wit_11_1 : words_string_entail_wit_11_1.
Proof.
  constructor; pre_process_default.
  replace i with n in * by lia.
  replace start with (-1) in * by lia.
  assert (Hfinal : output_rows_2 = words_output_rows_101 str_l).
  {
    apply split_scan_state_101_final_empty.
    replace (Zlength str_l) with n by (unfold string_length in *; lia).
    exact PreH23.
  }
  Exists output_ptrs_2 output_rows_2.
  unfold store_string.
  entailer!.
  - rewrite Hfinal.
    apply problem_101_spec_z_words_output_rows_101.
    exact PreH19.
Qed.

Lemma proof_of_words_string_entail_wit_11_2 : words_string_entail_wit_11_2.
Proof.
  constructor; pre_process_default.
  replace k with len in * by lia.
  replace (start + len) with n in * by lia.
  assert (Hrow_len : Zlength (word_row_101 str_l start n) = len + 1).
  {
    rewrite word_row_101_unfold.
    rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite Zlength_word_payload_101 by (unfold string_length in *; lia).
    lia.
  }
  assert (Hfinal :
    output_rows_2 ++ (word_row_101 str_l start n :: nil) =
    words_output_rows_101 str_l).
  {
    replace n with (Zlength str_l) by (unfold string_length in *; lia).
    apply split_scan_state_101_final_nonempty.
    - replace n with (Zlength str_l) in PreH24 by (unfold string_length in *; lia).
      exact PreH24.
    - unfold string_length in *; lia.
  }
  Exists (output_ptrs_2 ++ (w :: nil))
    (output_rows_2 ++ (word_row_101 str_l start n :: nil)).
  rewrite <- word_row_101_unfold.
  replace (len + 1) with (Zlength (word_row_101 str_l start n)) by lia.
  sep_apply (words_rows_heap_101_app_single
    output_ptrs_2 output_rows_2 w (word_row_101 str_l start n) ltac:(lia)).
  unfold store_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  entailer!.
  - rewrite Hfinal.
    apply problem_101_spec_z_words_output_rows_101.
    exact PreH20.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
       try (rewrite Hfinal; rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
       try (rewrite <- Hfinal; entailer!).
Qed.

Lemma proof_of_words_string_return_wit_1 : words_string_return_wit_1.
Proof.
  constructor; pre_process_default.
  Exists output_ptrs_2 output_rows_2 data_2.
  unfold store_string.
  replace (Zlength output_rows_2) with out_size by lia.
  replace (string_length str_l + 1) with (n + 1) by lia.
  entailer!.
  - rewrite PreH8.
    rewrite PreH16.
    replace (n + 1) with (Zlength str_l + 1) by (unfold string_length in *; lia).
    apply Zlength_words_output_rows_101_le.
Qed.
