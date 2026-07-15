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
From SimpleC.EE.CAV.ground_truth_p019_sort_numbers Require Import p019_sort_numbers_goal.
From SimpleC.EE.CAV.ground_truth_p019_sort_numbers Require Import p019_sort_numbers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p019_sort_numbers.
Local Open Scope sac.

Lemma proof_of_sort_numbers_safety_wit_181 : sort_numbers_safety_wit_181.
Proof.
  left.
  intros.
  entailer!.
Qed.
Lemma proof_of_sort_numbers_entail_wit_1 : sort_numbers_entail_wit_1.
Proof.
  unfold sort_numbers_entail_wit_1.
  right.
  intros.
  Intros.
  unfold number_words_chars_full_z, number_word_char_full_z,
    number_word_len_z, number_word_z, CharArray.full, store_array, c_string.
  simpl.
  entailer!.
Qed.

Lemma number_word_properties_19 :
  forall d, 0 <= d < 10 ->
    valid_string (number_word_z d) /\
    string_length (number_word_z d) = number_word_len_z d /\
    string_length (number_word_z d) < INT_MAX.
Proof.
  intros d Hd.
  destruct_digit_cases_19 d.
  all: unfold valid_string, all_ascii, no_inner_nul, string_length,
    number_word_len_z, number_word_z, Znth; rewrite Zlength_correct in *;
    simpl in *; repeat split;
    try reflexivity; try lia.
  all: try intros i Hi.
  all: assert (HC : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia;
    destruct HC as [? | [? | [? | [? | ?]]]]; subst i; try lia; vm_compute.
  all: congruence.
Qed.

Lemma proof_of_sort_numbers_entail_wit_10 : sort_numbers_entail_wit_10.
Proof.
  unfold sort_numbers_entail_wit_10.
  right.
  intros.
  Intros.
  subst word.
  assert (Hneq : token_prefix_z i tlen l <> number_word_z d).
  { intro Heq.
    unfold strcmp_result in PreH2.
    destruct PreH2 as [x [_ [_ [_ [Hret _]]]]].
    rewrite Heq in Hret.
    lia. }
  assert (Hmiss : token_miss_prefix_z (d + 1) (token_prefix_z i tlen l)).
  { unfold token_miss_prefix_z in *.
    intros k Hk.
    destruct (Z.eq_dec k d) as [-> | Hne]; [exact Hneq |].
    apply PreH49.
    lia. }
  assert (Hnext_bounds :
    0 <= Znth (d + 1) cnts_2 0 <= len + 1).
  { unfold scan_counts_z in PreH50.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct_digit_cases_19 d; simpl in *.
    all: try lia.
    assert (Hlen : List.length cnts_2 = 10%nat).
    { apply Nat2Z.inj.
      rewrite Zlength_correct in PreH38.
      simpl. exact PreH38. }
    unfold Znth; simpl; rewrite nth_overflow; lia. }
  assert (Hcstr :
    c_string (token_prefix_z i tlen l) =
      List.app (token_prefix_z i tlen l) (0 :: nil)).
  { unfold c_string. reflexivity. }
  assert (Hnext_word := number_word_properties_19 (d + 1)).
  destruct_digit_cases_19 d; simpl in *.
  all: try specialize (Hnext_word ltac:(lia)).
  all: entailer!.
  all: unfold number_words_full, number_words_missing,
    number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_ptrs_z,
    number_word_len_z, number_word_z, store_string, c_string in *;
    simpl in *; entailer!.
  all: eapply derivable1_trans;
    [apply derivable1_sepcon_mono; [cancel |
      match goal with
      | |- context [PtrArray.missing_i ?x ?n 0 ?m ?ls] =>
          apply (PtrArray.missing_i_merge_to_full x n m (Znth n ls 0) ls);
          lia
      end]
    | rewrite replace_Znth_Znth by lia; cancel].
  all: try rewrite H; cancel.
Qed.

Lemma token_prefix_zero_19 :
  forall i input, token_prefix_z i 0 input = nil.
Proof.
  intros.
  unfold token_prefix_z.
  simpl.
  replace (i - 0) with i by lia.
  apply Zsublist_nil.
  lia.
Qed.

Lemma scan_word_start_succ_19 :
  forall i input, 0 <= i ->
    scan_word_start_z (i + 1) input =
      if Z.eqb (scan_char_z i input) 32
      then i + 1
      else scan_word_start_z i input.
Proof.
  intros i input Hi.
  unfold scan_word_start_z at 1.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  2:{ rewrite Z2Nat.inj_add by lia. simpl. lia. }
  simpl.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma split_spaces_trailing_space_aux_19 :
  forall current input,
    SplitOnSpacesZ_aux_19 current (List.app input (32 :: nil)) =
    SplitOnSpacesZ_aux_19 current input.
Proof.
  intros current input.
  revert current.
  induction input as [|a input IH]; intros current; simpl.
  - destruct current; reflexivity.
  - destruct (Z.eqb a 32); destruct current; simpl; rewrite IH; reflexivity.
Qed.

Lemma count_word_trailing_space_19 :
  forall d input,
    count_word_in_string d (List.app input (32 :: nil)) =
    count_word_in_string d input.
Proof.
  intros.
  unfold count_word_in_string, SplitOnSpacesZ_19.
  rewrite split_spaces_trailing_space_aux_19.
  reflexivity.
Qed.

Lemma scan_completed_space_zero_19 :
  forall i input,
    0 <= i <= Zlength input ->
    scan_char_z i input = 32 ->
    forall d,
      count_word_in_string d (scan_completed_prefix_z (i + 1) 0 input) =
      count_word_in_string d (scan_completed_prefix_z i 0 input).
Proof.
  intros i input Hi Hchar d.
  unfold scan_completed_prefix_z.
  simpl.
  replace (i + 1 - 0) with (i + 1) by lia.
  replace (i - 0) with i by lia.
  destruct (Z_lt_dec i (Zlength input)) as [Hlt | Hge].
  - rewrite Z.min_l by lia.
    rewrite Z.min_l by lia.
    unfold scan_char_z in Hchar.
    assert (Hb : Z.ltb i (Zlength input) = true) by (apply Z.ltb_lt; lia).
    rewrite Hb in Hchar.
    rewrite (helper_sublist_snoc_Z input i 0) by lia.
    rewrite Hchar.
    apply count_word_trailing_space_19.
  - assert (i = Zlength input) by lia; subst i.
    rewrite !Z.min_r by lia.
    reflexivity.
Qed.

Lemma token_reset_facts_19 :
  forall i input,
    0 <= i -> scan_char_z i input = 32 ->
    token_empty_start_z (i + 1) 0 input /\
    token_unsat_end_z (i + 1) 0 input /\
    token_sat_start_z (i + 1) 0 input.
Proof.
  intros i input Hi Hchar.
  unfold token_empty_start_z, token_unsat_end_z, token_sat_start_z.
  repeat split; intros; try lia.
  left.
  rewrite scan_word_start_succ_19 by lia.
  rewrite Hchar.
  reflexivity.
Qed.

Lemma scan_counts_advance_19 :
  forall i input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    i <= Zlength input ->
    scan_counts_z i input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
    scan_counts_z (i + 1) input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.
Proof.
  intros.
  unfold scan_counts_z, scan_counts_capacity_z in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; lia.
Qed.

Lemma scan_counts_exact_reset_19 :
  forall i input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9,
    0 <= i <= Zlength input ->
    scan_char_z i input = 32 ->
    scan_counts_exact_z i 0 input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 ->
    scan_counts_exact_z (i + 1) 0 input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9.
Proof.
  intros i input c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 Hi Hchar Hexact.
  unfold scan_counts_exact_z in *.
  repeat split;
    rewrite scan_completed_space_zero_19 by assumption;
    tauto.
Qed.

Definition byte_range_19 (z : Z) : Prop := 0 <= z <= 127.

Lemma ascii_of_z_space_19 : forall z,
  byte_range_19 z ->
  (ascii_of_z_19 z = " "%char <-> z = 32).
Proof.
  intros z Hz; unfold byte_range_19 in Hz.
  split; intro H.
  - apply (f_equal nat_of_ascii) in H.
    unfold ascii_of_z_19 in H.
    rewrite nat_ascii_embedding in H by lia.
    apply Z2Nat.inj; try lia; exact H.
  - subst z; reflexivity.
Qed.

Lemma string_ascii_map_19 : forall l,
  string_of_list_ascii (map ascii_of_z_19 l) = string_of_list_z_19 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma split_spaces_commute_aux_19 : forall input current,
  Forall byte_range_19 input ->
  Forall byte_range_19 current ->
  SplitOnSpaces_aux_19 (map ascii_of_z_19 current)
    (string_of_list_z_19 input) =
  map string_of_list_z_19 (SplitOnSpacesZ_aux_19 current input).
Proof.
  induction input as [|a input IH]; intros current Hinput Hcurrent.
  - destruct current as [|c current]; simpl; [reflexivity|].
    assert (Hword :
      string_of_list_ascii (rev (map ascii_of_z_19 (c :: current))) =
      string_of_list_z_19 (rev (c :: current))).
    { rewrite <- map_rev. apply string_ascii_map_19. }
    change (string_of_list_ascii (rev (map ascii_of_z_19 (c :: current))) :: nil =
      string_of_list_z_19 (rev (c :: current)) :: nil).
    rewrite Hword; reflexivity.
  - inversion Hinput as [|? ? Ha Htail]; subst.
    simpl.
    destruct (Z.eq_dec a 32) as [-> | Hne].
    + simpl.
      destruct current as [|c current]; simpl.
      * apply (IH nil); [exact Htail | constructor].
      * assert (Hword :
          string_of_list_ascii (rev (map ascii_of_z_19 (c :: current))) =
          string_of_list_z_19 (rev (c :: current))).
        { rewrite <- map_rev. apply string_ascii_map_19. }
        change (
          string_of_list_ascii (rev (map ascii_of_z_19 (c :: current))) ::
            SplitOnSpaces_aux_19 nil (string_of_list_z_19 input) =
          string_of_list_z_19 (rev (c :: current)) ::
            map string_of_list_z_19 (SplitOnSpacesZ_aux_19 nil input)).
        rewrite Hword. f_equal.
        apply (IH nil); [exact Htail | constructor].
    + assert (Hascii : ascii_of_z_19 a <> " "%char).
      { intro Heq. apply ascii_of_z_space_19 in Heq; auto. }
      assert (Hb : Z.eqb a 32 = false) by (apply Z.eqb_neq; exact Hne).
      rewrite Hb.
      destruct (ascii_dec (ascii_of_z_19 a) " "%char) as [Heq | _];
        [contradiction |].
      apply (IH (a :: current)); [exact Htail | constructor; assumption].
Qed.

Lemma split_spaces_commute_19 : forall input,
  Forall byte_range_19 input ->
  SplitOnSpaces_19 (string_of_list_z_19 input) =
  map string_of_list_z_19 (SplitOnSpacesZ_19 input).
Proof.
  intros input Hinput.
  unfold SplitOnSpaces_19, SplitOnSpacesZ_19.
  apply (split_spaces_commute_aux_19 input nil); auto.
Qed.

Lemma split_concat_valid_19 : forall words,
  Forall is_valid_word words ->
  SplitOnSpaces_19 (String.concat " " words) = words.
Proof.
  intros words Hvalid.
  induction Hvalid as [|w words Hw Hwords IH].
  - reflexivity.
  - unfold is_valid_word in Hw.
    destruct Hw as [n Hw].
    inversion Hw; subst; destruct words; simpl in *; try reflexivity.
    all: cbn [SplitOnSpaces_19 SplitOnSpaces_aux_19 String.append];
      repeat destruct ascii_dec; try congruence;
      f_equal; exact IH.
Qed.

Lemma ascii_range_forall_19 : forall input,
  ascii_range_z input -> Forall byte_range_19 input.
Proof.
  intros input Hrange.
  apply Forall_forall. intros x Hx.
  destruct (In_nth input x 0 Hx) as [n [Hn Hnth]].
  specialize (Hrange (Z.of_nat n)).
  assert (0 <= Z.of_nat n < Zlength input).
  { rewrite Zlength_correct. lia. }
  specialize (Hrange H).
  unfold Znth in Hrange.
  rewrite Nat2Z.id in Hrange.
  rewrite Hnth in Hrange.
  exact Hrange.
Qed.

Lemma problem_pre_split_valid_19 : forall input,
  ascii_range_z input -> problem_19_pre_z input ->
  Forall (fun w => is_valid_word (string_of_list_z_19 w))
    (SplitOnSpacesZ_19 input).
Proof.
  intros input Hrange Hpre.
  unfold problem_19_pre_z, problem_19_pre in Hpre.
  destruct Hpre as [words [Hspace Hvalid]].
  assert (Hcomm := split_spaces_commute_aux_19 input nil
    (ascii_range_forall_19 input Hrange) (Forall_nil byte_range_19)).
  change (SplitOnSpaces_19 (string_of_list_z_19 input) =
    map string_of_list_z_19 (SplitOnSpacesZ_19 input)) in Hcomm.
  unfold SpaceDelimited in Hspace.
  rewrite <- Hspace in Hcomm.
  rewrite split_concat_valid_19 in Hcomm by exact Hvalid.
  rewrite Hcomm in Hvalid.
  remember (SplitOnSpacesZ_19 input) as groups eqn:Hg.
  clear Hcomm Hg Hspace Hrange.
  induction groups as [|g groups IH]; simpl in Hvalid.
  - constructor.
  - inversion Hvalid; subst. constructor; auto.
Qed.

Fixpoint scan_current_rev_19 (fuel : nat) (input : list Z) : list Z :=
  match fuel with
  | O => nil
  | S fuel' =>
      let prev := scan_current_rev_19 fuel' input in
      let pos := Z.of_nat fuel' in
      if Z.eqb (scan_char_z pos input) 32 then nil
      else scan_char_z pos input :: prev
  end.

Lemma split_scan_state_19 : forall n input,
  (n <= length input)%nat ->
  exists done,
    SplitOnSpacesZ_19 input =
      List.app done (SplitOnSpacesZ_aux_19 (scan_current_rev_19 n input)
        (skipn n input)).
Proof.
  induction n as [|n IH]; intros input Hn.
  - exists nil. reflexivity.
  - assert (Hlt : (n < length input)%nat) by lia.
    destruct (IH input ltac:(lia)) as [done Hstate].
    destruct (skipn n input) as [|a tail] eqn:Hskip.
    { assert (Datatypes.length (skipn n input) = 0%nat) by
        (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. lia. }
    assert (Hnth : nth n input 0 = a).
    { pose proof (nth_skipn n input 0 0) as Hnth.
      rewrite Hskip in Hnth. simpl in Hnth.
      replace (n + 0)%nat with n in Hnth by lia. symmetry; exact Hnth. }
    assert (Hscan : scan_char_z (Z.of_nat n) input = a).
    { unfold scan_char_z.
      assert (Hb : Z.ltb (Z.of_nat n) (Zlength input) = true).
      { apply Z.ltb_lt. rewrite Zlength_correct. lia. }
      rewrite Hb. unfold Znth. rewrite Nat2Z.id. exact Hnth. }
    assert (Htail : skipn (S n) input = tail).
    { replace (S n) with (1 + n)%nat by lia.
      rewrite <- skipn_skipn, Hskip. reflexivity. }
    simpl scan_current_rev_19.
    rewrite Hscan, Htail.
    destruct (Z.eq_dec a 32) as [-> | Hne].
    + simpl.
      destruct (scan_current_rev_19 n input) as [|c current] eqn:Hcur.
      * exists done. exact Hstate.
      * exists (List.app done ((rev (c :: current)) :: nil)).
        rewrite Hstate. simpl.
        rewrite <- app_assoc. reflexivity.
    + assert (Hb : Z.eqb a 32 = false) by (apply Z.eqb_neq; exact Hne).
      rewrite Hb.
      exists done. rewrite Hstate. simpl. rewrite Hb. reflexivity.
Qed.

Lemma scan_word_start_bounds_19 : forall n input,
  0 <= scan_word_start_nat n input <= Z.of_nat n.
Proof.
  induction n as [|n IH]; intros input; simpl.
  - lia.
  - pose proof (IH input).
    destruct (Z.eqb (scan_char_z (Z.of_nat n) input) 32); lia.
Qed.

Lemma scan_current_segment_19 : forall n input,
  (n <= length input)%nat ->
  rev (scan_current_rev_19 n input) =
    sublist (scan_word_start_nat n input) (Z.of_nat n) input.
Proof.
  induction n as [|n IH]; intros input Hn.
  - simpl. symmetry. apply Zsublist_nil. lia.
  - assert (Hlt : Z.of_nat n < Zlength input).
    { rewrite Zlength_correct. lia. }
    assert (Hscan : scan_char_z (Z.of_nat n) input =
      Znth (Z.of_nat n) input 0).
    { unfold scan_char_z.
      assert (Hb : Z.ltb (Z.of_nat n) (Zlength input) = true)
        by (apply Z.ltb_lt; exact Hlt).
      rewrite Hb. reflexivity. }
    simpl scan_current_rev_19.
    simpl scan_word_start_nat.
    destruct (Z.eq_dec (scan_char_z (Z.of_nat n) input) 32)
      as [Hspace | Hnon].
    + assert (Hb : Z.eqb (scan_char_z (Z.of_nat n) input) 32 = true)
        by (apply Z.eqb_eq; exact Hspace).
      rewrite Hb. simpl.
      symmetry. apply Zsublist_nil. lia.
    + assert (Hb : Z.eqb (scan_char_z (Z.of_nat n) input) 32 = false)
        by (apply Z.eqb_neq; exact Hnon).
      rewrite Hb. simpl.
      rewrite (IH input) by lia.
      replace (Z.pos (Pos.of_succ_nat n)) with (Z.of_nat n + 1) by lia.
      rewrite (sublist_split (scan_word_start_nat n input)
        (Z.of_nat n + 1) (Z.of_nat n) input) by
        (pose proof (scan_word_start_bounds_19 n input); lia).
      rewrite (sublist_single 0) by lia.
      rewrite <- Hscan. reflexivity.
Qed.

Lemma scan_token_in_split_19 : forall i tlen input,
  0 <= i <= Zlength input ->
  scan_char_z i input = 32 ->
  0 < tlen < 31 ->
  token_unsat_end_z i tlen input ->
  In (token_prefix_z i tlen input) (SplitOnSpacesZ_19 input).
Proof.
  intros i tlen input Hi Hchar Htlen Hunsat.
  assert (Hinat : Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
  assert (Hnlen : (Z.to_nat i <= length input)%nat).
  { rewrite <- Nat2Z.id. rewrite <- Zlength_correct.
    apply Nat2Z.inj_le. rewrite Hinat. lia. }
  unfold token_unsat_end_z in Hunsat.
  destruct Hunsat as [Hzero | Hend]; [lia |].
  assert (Htoken : token_prefix_z i tlen input =
    sublist (scan_word_start_z i input) i input).
  { unfold token_prefix_z.
    assert (Hb : Z.ltb tlen 31 = true) by (apply Z.ltb_lt; lia).
    rewrite Hb. replace (i - tlen) with (scan_word_start_z i input) by lia.
    reflexivity. }
  pose proof (scan_current_segment_19 (Z.to_nat i) input Hnlen) as Hseg.
  rewrite Hinat in Hseg.
  change (rev (scan_current_rev_19 (Z.to_nat i) input) =
    sublist (scan_word_start_z i input) i input) in Hseg.
  assert (Hcur : scan_current_rev_19 (Z.to_nat i) input <> nil).
  { intro Hnil. rewrite Hnil in Hseg. simpl in Hseg.
    assert (Hbounds : 0 <= scan_word_start_z i input <= i).
    { unfold scan_word_start_z.
      pose proof (scan_word_start_bounds_19 (Z.to_nat i) input).
      rewrite Hinat in H. exact H. }
    pose proof (sublist_length (scan_word_start_z i input) i input
      ltac:(lia) ltac:(lia)) as Hlen.
    rewrite <- Hseg in Hlen. simpl in Hlen.
    replace (i - scan_word_start_z i input) with tlen in Hlen by lia.
    assert (Z.to_nat tlen <> 0%nat).
    { intro E. pose proof (Z2Nat.id tlen ltac:(lia)) as Et.
      rewrite E in Et. simpl in Et. lia. }
    lia. }
  destruct (split_scan_state_19 (Z.to_nat i) input Hnlen)
    as [done Hstate].
  assert (Hinrev : In (rev (scan_current_rev_19 (Z.to_nat i) input))
    (SplitOnSpacesZ_19 input)).
  { destruct (Z_lt_dec i (Zlength input)) as [Hlt | Hge].
    - destruct (skipn (Z.to_nat i) input) as [|a tail] eqn:Hskip.
      { assert (length (skipn (Z.to_nat i) input) = 0%nat) by
          (rewrite Hskip; reflexivity).
        rewrite length_skipn in H. rewrite Zlength_correct in Hlt. lia. }
      assert (Hnth : nth (Z.to_nat i) input 0 = a).
      { pose proof (nth_skipn (Z.to_nat i) input 0 0) as Hnth.
        rewrite Hskip in Hnth. simpl in Hnth.
        replace (Z.to_nat i + 0)%nat with (Z.to_nat i) in Hnth by lia.
        symmetry; exact Hnth. }
      assert (Ha : a = 32).
      { unfold scan_char_z in Hchar.
        assert (Hb : Z.ltb i (Zlength input) = true)
          by (apply Z.ltb_lt; exact Hlt).
        rewrite Hb in Hchar. unfold Znth in Hchar.
        rewrite Hnth in Hchar. exact Hchar. }
      assert (Hnth32 : nth (Z.to_nat i) input 0 = 32) by
        (rewrite Hnth; exact Ha).
      subst a.
      destruct (scan_current_rev_19 (Z.to_nat i) input)
        as [|c current] eqn:Hcurrent; [contradiction |].
      rewrite Hstate. rewrite Hnth32. simpl.
      apply in_or_app. right. left. reflexivity.
    - assert (i = Zlength input) by lia; subst i.
      assert (Hskip : skipn (Z.to_nat (Zlength input)) input = nil).
      { apply skipn_all2. rewrite Zlength_correct, Nat2Z.id. lia. }
      rewrite Hskip in Hstate.
      destruct (scan_current_rev_19 (Z.to_nat (Zlength input)) input)
        as [|c current] eqn:Hcurrent; [contradiction |].
      rewrite Hstate. simpl.
      apply in_or_app. right. left. reflexivity. }
  rewrite Htoken, <- Hseg.
  exact Hinrev.
Qed.

Lemma scan_current_group_in_split_19 : forall i input,
  0 <= i <= Zlength input -> scan_char_z i input = 32 ->
  scan_current_rev_19 (Z.to_nat i) input <> nil ->
  In (rev (scan_current_rev_19 (Z.to_nat i) input))
    (SplitOnSpacesZ_19 input).
Proof.
  intros i input Hi Hchar Hcur.
  assert (Hinat : Z.of_nat (Z.to_nat i) = i) by (apply Z2Nat.id; lia).
  assert (Hnlen : (Z.to_nat i <= length input)%nat).
  { rewrite <- Nat2Z.id. rewrite <- Zlength_correct.
    apply Nat2Z.inj_le. rewrite Hinat. lia. }
  destruct (split_scan_state_19 (Z.to_nat i) input Hnlen)
    as [done Hstate].
  destruct (Z_lt_dec i (Zlength input)) as [Hlt | Hge].
  - destruct (skipn (Z.to_nat i) input) as [|a tail] eqn:Hskip.
    { assert (length (skipn (Z.to_nat i) input) = 0%nat) by
        (rewrite Hskip; reflexivity).
      rewrite length_skipn in H. rewrite Zlength_correct in Hlt. lia. }
    assert (Hnth : nth (Z.to_nat i) input 0 = a).
    { pose proof (nth_skipn (Z.to_nat i) input 0 0) as Hnth.
      rewrite Hskip in Hnth. simpl in Hnth.
      replace (Z.to_nat i + 0)%nat with (Z.to_nat i) in Hnth by lia.
      symmetry; exact Hnth. }
    assert (Ha : a = 32).
    { unfold scan_char_z in Hchar.
      assert (Hb : Z.ltb i (Zlength input) = true)
        by (apply Z.ltb_lt; exact Hlt).
      rewrite Hb in Hchar. unfold Znth in Hchar.
      rewrite Hnth in Hchar. exact Hchar. }
    assert (Hnth32 : nth (Z.to_nat i) input 0 = 32) by
      (rewrite Hnth; exact Ha).
    subst a.
    destruct (scan_current_rev_19 (Z.to_nat i) input)
      as [|c current] eqn:Hcurrent; [contradiction |].
    rewrite Hstate. rewrite Hnth32. simpl.
    apply in_or_app. right. left. reflexivity.
  - assert (i = Zlength input) by lia; subst i.
    assert (Hskip : skipn (Z.to_nat (Zlength input)) input = nil).
    { apply skipn_all2. rewrite Zlength_correct, Nat2Z.id. lia. }
    rewrite Hskip in Hstate.
    destruct (scan_current_rev_19 (Z.to_nat (Zlength input)) input)
      as [|c current] eqn:Hcurrent; [contradiction |].
    rewrite Hstate. simpl.
    apply in_or_app. right. left. reflexivity.
Qed.

Lemma string_z_inj_range_19 : forall l1 l2,
  Forall byte_range_19 l1 -> Forall byte_range_19 l2 ->
  string_of_list_z_19 l1 = string_of_list_z_19 l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; destruct l2 as [|b l2]; simpl; intros H1 H2 Heq;
    try discriminate; try reflexivity.
  inversion H1 as [|? ? Ha Htl1]; subst.
  inversion H2 as [|? ? Hb Htl2]; subst.
  injection Heq as Hhead Htail.
  f_equal.
  - apply (f_equal nat_of_ascii) in Hhead.
    unfold ascii_of_z_19 in Hhead.
    rewrite !nat_ascii_embedding in Hhead by
      (unfold byte_range_19 in *; lia).
    apply Z2Nat.inj; try (unfold byte_range_19 in *; lia); exact Hhead.
  - apply IH; assumption.
Qed.

Lemma valid_token_number_word_19 : forall token,
  Forall byte_range_19 token ->
  is_valid_word (string_of_list_z_19 token) ->
  exists k, 0 <= k < 10 /\ token = number_word_z k.
Proof.
  intros token Hrange [n Hword].
  exists (Z.of_nat n).
  inversion Hword; subst.
  all: split; [lia |].
  all: apply string_z_inj_range_19; [exact Hrange | | symmetry; assumption].
  all: simpl; repeat constructor; unfold byte_range_19; lia.
Qed.

Lemma Forall_skipn_19 : forall (P : Z -> Prop) n l,
  Forall P l -> Forall P (skipn n l).
Proof.
  intros P n; induction n as [|n IH]; intros l H; simpl; auto.
  destruct l; simpl; auto. inversion H; auto.
Qed.

Lemma Forall_firstn_19 : forall (P : Z -> Prop) n l,
  Forall P l -> Forall P (firstn n l).
Proof.
  intros P n; induction n as [|n IH]; intros l H; simpl; auto.
  destruct l; simpl; auto. inversion H; constructor; auto.
Qed.

Lemma Forall_sublist_19 : forall (P : Z -> Prop) lo hi l,
  Forall P l -> Forall P (sublist lo hi l).
Proof.
  intros. unfold sublist.
  apply Forall_skipn_19, Forall_firstn_19. exact H.
Qed.

Lemma strcmp_zero_eq_19 : forall s1 s2,
  valid_string s1 -> valid_string s2 ->
  strcmp_result s1 s2 0 -> s1 = s2.
Proof.
  intros s1 s2 Hv1 Hv2 Hcmp.
  unfold strcmp_result in Hcmp.
  destruct Hcmp as [q [Hq1 [Hq2 [Hpref [Hret Hend]]]]].
  destruct Hend as [Hz1 | Hne].
  - assert (Hqeq1 : q = string_length s1).
    { apply helper_c_string_zero_index; [exact Hv1 | lia | exact Hz1]. }
    assert (Hz2 : Znth q (c_string s2) 0 = 0) by lia.
    assert (Hqeq2 : q = string_length s2).
    { apply helper_c_string_zero_index; [exact Hv2 | lia | exact Hz2]. }
    assert (Hlen : length s1 = length s2).
    { unfold string_length in Hqeq1, Hqeq2.
      rewrite !Zlength_correct in Hqeq1, Hqeq2. lia. }
    apply nth_ext with (d := 0) (d' := 0).
    + exact Hlen.
    + intros n Hn.
      specialize (Hpref (Z.of_nat n) ltac:(
        unfold string_length in Hqeq1; rewrite Zlength_correct in Hqeq1; lia)).
      rewrite (c_string_Znth_inside s1 (Z.of_nat n) 0) in Hpref by
        (unfold string_length; rewrite Zlength_correct; lia).
      rewrite (c_string_Znth_inside s2 (Z.of_nat n) 0) in Hpref by
        (unfold string_length; rewrite Zlength_correct; rewrite <- Hlen; lia).
      unfold Znth in Hpref. rewrite Nat2Z.id in Hpref. exact Hpref.
  - assert (Znth q (c_string s1) 0 = Znth q (c_string s2) 0) by lia.
    contradiction.
Qed.

Lemma split_spaces_boundary_append_aux_19 : forall prefix rest current,
  SplitOnSpacesZ_aux_19 current
    (List.app (List.app prefix (32 :: nil)) rest) =
  List.app (SplitOnSpacesZ_aux_19 current
    (List.app prefix (32 :: nil)))
    (SplitOnSpacesZ_aux_19 nil rest).
Proof.
  induction prefix as [|a prefix IH]; intros rest current; simpl.
  - destruct current; reflexivity.
  - destruct (Z.eqb a 32); destruct current; simpl; try apply IH.
    f_equal. apply IH.
Qed.

Lemma split_spaces_boundary_append_19 : forall prefix rest,
  split_boundary_z prefix ->
  SplitOnSpacesZ_19 (List.app prefix rest) =
  List.app (SplitOnSpacesZ_19 prefix) (SplitOnSpacesZ_19 rest).
Proof.
  intros prefix rest [-> | [pre ->]].
  - reflexivity.
  - unfold SplitOnSpacesZ_19.
    apply split_spaces_boundary_append_aux_19.
Qed.

Lemma split_number_word_space_19 : forall d,
  0 <= d < 10 ->
  SplitOnSpacesZ_19 (List.app (number_word_z d) (32 :: nil)) =
    number_word_z d :: nil.
Proof.
  intros d Hd. destruct_digit_cases_19 d;
    unfold SplitOnSpacesZ_19, number_word_z; reflexivity.
Qed.

Lemma count_word_boundary_append_19 : forall k d prefix,
  0 <= d < 10 -> split_boundary_z prefix ->
  count_word_in_string k
    (List.app prefix (List.app (number_word_z d) (32 :: nil))) =
  count_word_in_string k prefix +
    (if list_Z_eq_dec_19 (number_word_z d) (number_word_z k)
     then 1 else 0).
Proof.
  intros k d prefix Hd Hboundary.
  unfold count_word_in_string.
  rewrite split_spaces_boundary_append_19 by exact Hboundary.
  rewrite split_number_word_space_19 by exact Hd.
  rewrite count_occ_app. simpl.
  destruct (list_Z_eq_dec_19 (number_word_z d) (number_word_z k)); lia.
Qed.

Lemma scan_start_boundary_19 : forall n input,
  (n <= length input)%nat ->
  split_boundary_z (sublist 0 (scan_word_start_nat n input) input).
Proof.
  induction n as [|n IH]; intros input Hn; simpl.
  - left. apply Zsublist_nil. lia.
  - destruct (Z.eq_dec (scan_char_z (Z.of_nat n) input) 32)
      as [Hspace | Hnon].
    + assert (Hb : Z.eqb (scan_char_z (Z.of_nat n) input) 32 = true)
        by (apply Z.eqb_eq; exact Hspace).
      rewrite Hb.
      right. exists (sublist 0 (Z.of_nat n) input).
      rewrite (helper_sublist_snoc_Z input (Z.of_nat n) 0) by
        (rewrite Zlength_correct; lia).
      unfold scan_char_z in Hspace.
      assert (Hlt : Z.ltb (Z.of_nat n) (Zlength input) = true)
        by (apply Z.ltb_lt; rewrite Zlength_correct; lia).
      rewrite Hlt in Hspace. rewrite Hspace. reflexivity.
    + assert (Hb : Z.eqb (scan_char_z (Z.of_nat n) input) 32 = false)
        by (apply Z.eqb_neq; exact Hnon).
      rewrite Hb. apply IH. lia.
Qed.

Lemma count_word_boundary_append_bare_19 : forall k d prefix,
  0 <= d < 10 -> split_boundary_z prefix ->
  count_word_in_string k (List.app prefix (number_word_z d)) =
  count_word_in_string k prefix +
    (if list_Z_eq_dec_19 (number_word_z d) (number_word_z k)
     then 1 else 0).
Proof.
  intros k d prefix Hd Hboundary.
  transitivity (count_word_in_string k
    (List.app (List.app prefix (number_word_z d)) (32 :: nil))).
  - symmetry. apply count_word_trailing_space_19.
  -
  rewrite <- app_assoc.
  apply count_word_boundary_append_19; assumption.
Qed.

Lemma scan_completed_match_count_19 : forall k d i tlen input,
  0 <= i <= Zlength input -> scan_char_z i input = 32 ->
  0 < tlen < 31 -> tlen <= i -> token_unsat_end_z i tlen input ->
  token_prefix_z i tlen input = number_word_z d ->
  0 <= d < 10 ->
  count_word_in_string k (scan_completed_prefix_z (i + 1) 0 input) =
  count_word_in_string k (scan_completed_prefix_z i tlen input) +
    (if list_Z_eq_dec_19 (number_word_z d) (number_word_z k)
     then 1 else 0).
Proof.
  intros k d i tlen input Hi Hchar Htlen Htle Hunsat Htoken Hd.
  unfold token_unsat_end_z in Hunsat.
  destruct Hunsat as [Hz | Hend]; [lia |].
  assert (Hstart : i - tlen = scan_word_start_z i input) by lia.
  assert (Hnat : (Z.to_nat i <= length input)%nat).
  { rewrite <- Nat2Z.id, <- Zlength_correct.
    apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
  assert (Hboundary :
    split_boundary_z (sublist 0 (i - tlen) input)).
  { rewrite Hstart. unfold scan_word_start_z.
    apply scan_start_boundary_19. exact Hnat. }
  assert (Hstart_bounds : 0 <= i - tlen <= i) by lia.
  unfold token_prefix_z in Htoken.
  assert (Htb : Z.ltb tlen 31 = true) by (apply Z.ltb_lt; lia).
  rewrite Htb in Htoken.
  unfold scan_completed_prefix_z.
  rewrite Htb. simpl.
  rewrite (Z.min_l (i - tlen) (Zlength input)) by lia.
  replace (i + 1 - 0) with (i + 1) by lia.
  destruct (Z_lt_dec i (Zlength input)) as [Hlt | Hge].
  - rewrite Z.min_l by lia.
    rewrite (sublist_split 0 (i + 1) i input) by lia.
    rewrite (sublist_split 0 i (i - tlen) input) by lia.
    rewrite Htoken.
    assert (Hzi : Znth i input 0 = 32).
    { unfold scan_char_z in Hchar.
      assert (Hb : Z.ltb i (Zlength input) = true)
        by (apply Z.ltb_lt; exact Hlt).
      rewrite Hb in Hchar. exact Hchar. }
    rewrite (sublist_single 0) by lia. rewrite Hzi.
    rewrite <- app_assoc.
    apply count_word_boundary_append_19; assumption.
  - assert (Heq : i = Zlength input) by lia.
    rewrite Z.min_r by lia.
    rewrite Heq at 1.
    rewrite (sublist_split 0 (Zlength input) (i - tlen) input) by lia.
    assert (Htoken' : sublist (i - tlen) (Zlength input) input =
      number_word_z d) by (rewrite <- Heq; exact Htoken).
    rewrite Htoken'.
    replace (Zlength input - tlen) with (i - tlen) by lia.
    apply count_word_boundary_append_bare_19; assumption.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_1 : sort_numbers_entail_wit_11_1.
Proof.
  unfold sort_numbers_entail_wit_11_1.
  right.
  intros.
  Intros.
  assert (Htlen0 : tlen = 0).
  { destruct (Z.eq_dec tlen 0) as [H | H]; [exact H |].
    exfalso.
    assert (Htpos : 0 < tlen) by lia.
    assert (Htlt31 : tlen < 31).
    { destruct (Z_lt_dec tlen 31); [assumption |].
      assert (Ht31 : tlen = 31) by lia; subst tlen.
      assert (Hsat : scan_word_start_z i l + 31 <= i).
      { apply PreH42. lia. }
      assert (Hnlen : (Z.to_nat i <= length l)%nat).
      { rewrite <- Nat2Z.id. rewrite <- Zlength_correct.
        apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia. }
      pose proof (scan_current_segment_19 (Z.to_nat i) l Hnlen) as Hseg.
      rewrite Z2Nat.id in Hseg by lia.
      change (rev (scan_current_rev_19 (Z.to_nat i) l) =
        sublist (scan_word_start_z i l) i l) in Hseg.
      assert (Hcur : scan_current_rev_19 (Z.to_nat i) l <> nil).
      { intro Hnil. rewrite Hnil in Hseg. simpl in Hseg.
        pose proof (sublist_length (scan_word_start_z i l) i l
          ltac:(pose proof (scan_word_start_bounds_19 (Z.to_nat i) l);
            unfold scan_word_start_z; lia)
          ltac:(lia)) as Hlen.
        rewrite <- Hseg in Hlen. simpl in Hlen.
        assert (Z.to_nat (i - scan_word_start_z i l) <> 0%nat).
        { intro E.
          pose proof (Z2Nat.id (i - scan_word_start_z i l) ltac:(lia)) as Et.
          rewrite E in Et. simpl in Et. lia. }
        lia. }
      assert (Hin := scan_current_group_in_split_19 i l ltac:(lia) PreH31 Hcur).
      assert (Hgroups := problem_pre_split_valid_19 l PreH10 PreH9).
      apply Forall_forall with
        (x := rev (scan_current_rev_19 (Z.to_nat i) l)) in Hgroups;
        [| exact Hin].
      assert (Hgroup_range :
        Forall byte_range_19 (rev (scan_current_rev_19 (Z.to_nat i) l))).
      { rewrite Hseg. apply Forall_sublist_19, ascii_range_forall_19.
        exact PreH10. }
      destruct (valid_token_number_word_19 _ Hgroup_range Hgroups)
        as [k [Hk Heq]].
      assert (Hlong : 31 <= Zlength (rev (scan_current_rev_19 (Z.to_nat i) l))).
      { rewrite Hseg, Zlength_correct.
        rewrite sublist_length by
          (pose proof (scan_word_start_bounds_19 (Z.to_nat i) l);
           unfold scan_word_start_z; lia).
        rewrite Z2Nat.id by lia. lia. }
      rewrite Heq in Hlong.
      destruct_digit_cases_19 k; unfold number_word_z in Hlong;
        rewrite Zlength_correct in Hlong; simpl in Hlong; lia. }
    assert (Hunsat : token_unsat_end_z i tlen l).
    { apply PreH41. exact Htlt31. }
    assert (Hin : In (token_prefix_z i tlen l) (SplitOnSpacesZ_19 l)).
    { apply scan_token_in_split_19; try assumption; lia. }
    assert (Hgroups := problem_pre_split_valid_19 l PreH10 PreH9).
    apply Forall_forall with (x := token_prefix_z i tlen l) in Hgroups;
      [| exact Hin].
    assert (Htoken_range : Forall byte_range_19 (token_prefix_z i tlen l)).
    { unfold token_prefix_z.
      assert (Hb : Z.ltb tlen 31 = true) by (apply Z.ltb_lt; lia).
      rewrite Hb.
      apply Forall_sublist_19.
      apply ascii_range_forall_19. exact PreH10. }
    destruct (valid_token_number_word_19 _ Htoken_range Hgroups)
      as [k [Hk Heq]].
    specialize (PreH43 k ltac:(lia)).
    contradiction. }
  subst tlen.
  assert (Hprefix : token_prefix_z (i + 1) 0 l = nil)
    by apply token_prefix_zero_19.
  assert (Hreset := token_reset_facts_19 i l PreH11 PreH31).
  assert (Hcounts := scan_counts_advance_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH44).
  assert (Hexact := scan_counts_exact_reset_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH31 PreH45).
  entailer!.
  - rewrite token_prefix_zero_19. simpl.
    sep_apply CharArray.full_to_undef_full.
    sep_apply CharArray.undef_full_to_undef_seg.
    sep_apply (CharArray.undef_seg_merge_to_undef_full token 0 1 32).
    entailer!.
    replace (token + 0 * sizeof(CHAR)) with token by lia.
    replace (32 - 0) with 32 by lia.
    cancel.
    lia.
  - rewrite Hprefix. reflexivity.
  - rewrite Hprefix.
    unfold valid_string, all_ascii, no_inner_nul, string_length.
    rewrite Zlength_correct. simpl. repeat split; intros; lia.
  - rewrite Hprefix. unfold string_length. rewrite Zlength_correct. reflexivity.
  - rewrite Hprefix. unfold string_length. rewrite Zlength_correct. simpl. lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_2 : sort_numbers_entail_wit_11_2.
Proof.
  unfold sort_numbers_entail_wit_11_2.
  right.
  intros.
  Intros.
  subst retval word.
  assert (Htoken : token_prefix_z i tlen l = number_word_z d).
  { apply strcmp_zero_eq_19; assumption. }
  assert (Htlen : 0 < tlen < 31).
  { rewrite Htoken in PreH39.
    destruct_digit_cases_19 d; unfold number_word_z in PreH39;
      rewrite Zlength_correct in PreH39; simpl in PreH39; lia. }
  assert (Hunsat : token_unsat_end_z i tlen l) by (apply PreH47; lia).
  assert (Hreset := token_reset_facts_19 i l PreH15 PreH35).
  pose proof (scan_completed_match_count_19 0 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC0.
  pose proof (scan_completed_match_count_19 1 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC1.
  pose proof (scan_completed_match_count_19 2 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC2.
  pose proof (scan_completed_match_count_19 3 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC3.
  pose proof (scan_completed_match_count_19 4 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC4.
  pose proof (scan_completed_match_count_19 5 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC5.
  pose proof (scan_completed_match_count_19 6 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC6.
  pose proof (scan_completed_match_count_19 7 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC7.
  pose proof (scan_completed_match_count_19 8 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC8.
  pose proof (scan_completed_match_count_19 9 d i tlen l
    ltac:(lia) PreH35 Htlen PreH23 Hunsat Htoken ltac:(lia)) as HC9.
  assert (Hexact : scan_counts_exact_z (i + 1) 0 l
    (Znth 0 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 1 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 2 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 3 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 4 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 5 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 6 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 7 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 8 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 9 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)).
  { unfold scan_counts_exact_z in PreH51 |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct_digit_cases_19 d;
      repeat first [rewrite Znth_replace_Znth_Same by lia |
                    rewrite Znth_replace_Znth_Diff by lia];
      unfold number_word_z in HC0, HC1, HC2, HC3, HC4,
        HC5, HC6, HC7, HC8, HC9;
      simpl in HC0, HC1, HC2, HC3, HC4, HC5, HC6, HC7, HC8, HC9;
      repeat split; lia. }
  assert (Hcounts : scan_counts_z (i + 1) l
    (Znth 0 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 1 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 2 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 3 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 4 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 5 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 6 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 7 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 8 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)
    (Znth 9 (replace_Znth d (Znth d cnts_2 0 + 1) cnts_2) 0)).
  { unfold scan_counts_z, scan_counts_capacity_z in PreH50 |- *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct_digit_cases_19 d;
      repeat first [rewrite Znth_replace_Znth_Same by lia |
                    rewrite Znth_replace_Znth_Diff by lia];
      unfold number_word_len_z, number_word_z in *;
      rewrite !Zlength_correct in *; cbn [List.length] in *;
      repeat split; lia. }
  entailer!.
  - rewrite PreH41.
    sep_apply (CharArray.full_to_undef_full token (tlen + 1)
      (c_string (token_prefix_z i tlen l))).
    sep_apply (CharArray.undef_full_to_undef_seg token (tlen + 1)).
    sep_apply (CharArray.undef_seg_merge_to_undef_full token 0
      (tlen + 1) 32).
    replace (token + 0 * sizeof(CHAR)) with token by lia.
    replace (32 - 0) with 32 by lia.
    unfold number_words_full, number_words_missing.
    replace ((&( "words")) + d * sizeof(PTR)) with
      ((&( "words")) + d * 4) by reflexivity.
    let ptrs := constr:(number_word_ptrs_z (&( "w0")) (&( "w1"))
      (&( "w2")) (&( "w3")) (&( "w4")) (&( "w5")) (&( "w6"))
      (&( "w7")) (&( "w8")) (&( "w9"))) in
    let pc := constr:(((&( "words")) + d * 4) # Ptr |-> Znth d ptrs 0) in
    let miss := constr:(PtrArray.missing_i (&( "words")) d 0 10 ptrs) in
    let frame := constr:(
      CharArray.full (Znth d ptrs 0) (string_length (number_word_z d) + 1)
        (c_string (number_word_z d)) **
      number_words_chars_missing_z d (Znth d ptrs 0)
        (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
        (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9")) **
      CharArray.undef_full token 32) in
    let ptrs2 := constr:(number_word_ptrs_z (&( "w0")) (&( "w1"))
      (&( "w2")) (&( "w3")) (&( "w4")) (&( "w5")) (&( "w6"))
      (&( "w7")) (&( "w8")) (&( "w9"))) in
    let frame2 := constr:(
      CharArray.full (Znth d ptrs2 0) (string_length (number_word_z d) + 1)
        (c_string (number_word_z d)) **
      number_words_chars_missing_z d (Znth d ptrs2 0)
        (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3")) (&( "w4"))
        (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8")) (&( "w9")) **
      CharArray.undef_full token 32) in
    let pc2 := constr:(((&( "words")) + d * 4) # Ptr |-> Znth d ptrs2 0) in
    let miss2 := constr:(PtrArray.missing_i (&( "words")) d 0 10 ptrs2) in
    assert (Hmerge : (pc2 ** miss2) ** frame2 |--
      PtrArray.full (&( "words")) 10
        (replace_Znth d (Znth d ptrs2 0) ptrs2) ** frame2).
    { apply derivable1_sepcon_mono; [| apply derivable1_refl].
      apply (PtrArray.missing_i_merge_to_full (&( "words")) d 10
        (Znth d (number_word_ptrs_z (&( "w0")) (&( "w1")) (&( "w2"))
          (&( "w3")) (&( "w4")) (&( "w5")) (&( "w6")) (&( "w7"))
          (&( "w8")) (&( "w9"))) 0)
        (number_word_ptrs_z (&( "w0")) (&( "w1")) (&( "w2")) (&( "w3"))
          (&( "w4")) (&( "w5")) (&( "w6")) (&( "w7")) (&( "w8"))
          (&( "w9")))); lia. }
    match goal with
    | |- ?P |-- ?R =>
        let Q := type of Hmerge in
        lazymatch Q with ?Q0 |-- ?M =>
          assert (Hreorder : P |-- Q0)
        end
    end.
    { unfold number_word_ptrs_z. entailer!.
      rewrite logic_equiv_sepcon_swap.
      apply derivable1_refl. }
    match goal with
    | |- ?P |-- ?R =>
        let Q := type of Hmerge in
        lazymatch Q with ?Q0 |-- ?M =>
          let HP := fresh "HP" in
          pose proof (derivable1_trans P Q0 M Hreorder Hmerge) as HP;
          refine (derivable1_trans P M R HP _)
        end
    end.
    rewrite replace_Znth_Znth by lia.
    unfold number_words_chars_full_z, number_words_chars_missing_z,
      number_word_char_full_z, number_word_ptrs_z,
      number_word_len_z, number_word_z, store_string, c_string in *.
    destruct_digit_cases_19 d; simpl in *; entailer!; cancel.
    all: lia.
  - rewrite token_prefix_zero_19. reflexivity.
  - rewrite Zlength_replace_Znth. exact PreH38.
  - rewrite token_prefix_zero_19. reflexivity.
  - rewrite token_prefix_zero_19. simpl.
    unfold valid_string, all_ascii, no_inner_nul, string_length.
    rewrite Zlength_correct. simpl. repeat split; intros; lia.
  - rewrite token_prefix_zero_19. reflexivity.
  - rewrite token_prefix_zero_19. unfold string_length.
    rewrite Zlength_correct. simpl. lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_3 : sort_numbers_entail_wit_11_3.
Proof.
  pre_process_default.
  assert (Htlen : tlen = 0) by lia.
  subst tlen.
  assert (Hchar : scan_char_z i l = 32).
  { unfold scan_char_z.
    assert (Hb : Z.ltb i (Zlength l) = true) by
      (apply Z.ltb_lt; lia).
    rewrite Hb.
    rewrite <- PreH2.
    rewrite app_Znth1 by lia.
    reflexivity. }
  assert (Hreset := token_reset_facts_19 i l PreH14 Hchar).
  assert (Hcounts := scan_counts_advance_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH41).
  assert (Hexact := scan_counts_exact_reset_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) Hchar PreH42).
  Exists cnts_2.
  entailer!.
  rewrite !token_prefix_zero_19.
  cancel.
  all: rewrite token_prefix_zero_19.
  all: try reflexivity.
  all: try unfold valid_string, all_ascii, no_inner_nul, string_length.
  all: rewrite Zlength_correct; simpl; repeat split; intros; lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_4 : sort_numbers_entail_wit_11_4.
Proof.
  pre_process_default.
  assert (Htlen : tlen = 0) by lia.
  subst tlen.
  assert (Hchar : scan_char_z i l = 32).
  { unfold scan_char_z.
    assert (Hb : Z.ltb i (Zlength l) = false) by
      (apply Z.ltb_ge; lia).
    rewrite Hb. reflexivity. }
  assert (Hreset := token_reset_facts_19 i l PreH12 Hchar).
  assert (Hcounts := scan_counts_advance_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH39).
  assert (Hexact := scan_counts_exact_reset_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) Hchar PreH40).
  Exists cnts_2.
  entailer!.
  rewrite !token_prefix_zero_19.
  cancel.
  all: rewrite token_prefix_zero_19.
  all: try reflexivity.
  all: try unfold valid_string, all_ascii, no_inner_nul, string_length.
  all: rewrite Zlength_correct; simpl; repeat split; intros; lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_5 : sort_numbers_entail_wit_11_5.
Proof.
  pre_process_default.
  assert (Hzi : Znth i (l +:: 0) 0 = Znth i l 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hchar : scan_char_z i l = Znth i l 0).
  { unfold scan_char_z.
    assert (Hb : Z.ltb i (Zlength l) = true) by
      (apply Z.ltb_lt; lia).
    rewrite Hb. reflexivity. }
  assert (Hnon : scan_char_z i l <> 32).
  { rewrite Hchar, <- Hzi. exact PreH3. }
  assert (Hstart : scan_word_start_z (i + 1) l = scan_word_start_z i l).
  { rewrite scan_word_start_succ_19 by lia.
    destruct (Z.eqb_spec (scan_char_z i l) 32); [contradiction | reflexivity]. }
  assert (Hprefix :
    token_prefix_z (i + 1) (tlen + 1) l =
      token_prefix_z i tlen l +:: Znth i (l +:: 0) 0).
  { assert (Ht : Z.ltb tlen 31 = true) by (apply Z.ltb_lt; lia).
    unfold token_prefix_z at 1 2. rewrite Ht.
    destruct (Z_lt_dec (tlen + 1) 31) as [Hlt | Hge].
    - assert (Ht' : Z.ltb (tlen + 1) 31 = true) by
        (apply Z.ltb_lt; lia).
      rewrite Ht'.
      replace (i + 1 - (tlen + 1)) with (i - tlen) by lia.
      rewrite (sublist_split (i - tlen) (i + 1) i l) by lia.
      rewrite (sublist_single 0) by lia.
      rewrite Hzi. reflexivity.
    - assert (Ht30 : tlen = 30) by lia. subst tlen.
      simpl. rewrite Hstart.
      assert (Hu := PreH40 ltac:(lia)).
      unfold token_unsat_end_z in Hu.
      destruct Hu as [Hu | Hu]; [lia |].
      assert (Hsi : scan_word_start_z i l = i - 30) by lia.
      rewrite Hsi.
      replace (i - 30 + 31) with (i + 1) by lia.
      rewrite (sublist_split (i - 30) (i + 1) i l) by lia.
      rewrite (sublist_single 0) by lia.
      rewrite Hzi. reflexivity. }
  assert (Hcompleted :
    scan_completed_prefix_z (i + 1) (tlen + 1) l =
      scan_completed_prefix_z i tlen l).
  { unfold scan_completed_prefix_z.
    assert (Ht : Z.ltb tlen 31 = true) by (apply Z.ltb_lt; lia).
    rewrite Ht.
    destruct (Z_lt_dec (tlen + 1) 31) as [Hlt | Hge].
    - assert (Ht' : Z.ltb (tlen + 1) 31 = true) by
        (apply Z.ltb_lt; lia).
      rewrite Ht'.
      replace (i + 1 - (tlen + 1)) with (i - tlen) by lia.
      reflexivity.
    - assert (Ht30 : tlen = 30) by lia. subst tlen.
      simpl. rewrite Hstart.
      assert (Hu := PreH40 ltac:(lia)).
      unfold token_unsat_end_z in Hu.
      destruct Hu as [Hu | Hu]; [lia |].
      f_equal. f_equal. lia. }
  assert (Hcounts := scan_counts_advance_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH42).
  assert (Hexact : scan_counts_exact_z (i + 1) (tlen + 1) l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0)).
  { unfold scan_counts_exact_z in PreH43 |- *.
    rewrite Hcompleted. exact PreH43. }
  assert (Hempty : token_empty_start_z (i + 1) (tlen + 1) l).
  { unfold token_empty_start_z. intros. lia. }
  assert (Hunsat : tlen + 1 < 31 ->
    token_unsat_end_z (i + 1) (tlen + 1) l).
  { intro Hlt. unfold token_unsat_end_z.
    right. rewrite Hstart.
    destruct (Z.eq_dec tlen 0) as [Hz | Hz].
    - subst tlen. unfold token_empty_start_z in PreH39.
      specialize (PreH39 eq_refl). destruct PreH39; lia.
    - assert (Hu := PreH40 ltac:(lia)).
      unfold token_unsat_end_z in Hu. destruct Hu; lia. }
  assert (Hsat : token_sat_start_z (i + 1) (tlen + 1) l).
  { unfold token_sat_start_z. intro H31. rewrite Hstart.
    assert (Ht30 : tlen = 30) by lia. subst tlen.
    assert (Hu := PreH40 ltac:(lia)).
    unfold token_unsat_end_z in Hu. destruct Hu; lia. }
  assert (Hrange : 0 <= Znth i (l +:: 0) 0 <= 127).
  { rewrite Hzi. apply PreH14. lia. }
  assert (Hvalid : valid_string (token_prefix_z (i + 1) (tlen + 1) l)).
  { rewrite Hprefix.
    unfold valid_string, all_ascii, no_inner_nul in *.
    destruct PreH36 as [Ha Hn]. split; intros k Hk;
      rewrite Zlength_app in Hk; simpl in Hk;
      destruct (Z_lt_dec k (Zlength (token_prefix_z i tlen l))).
    - rewrite app_Znth1 by lia. apply Ha. lia.
    - change (0 <= k < Zlength (token_prefix_z i tlen l) + 1) in Hk.
      assert (Hkeq : k = Zlength (token_prefix_z i tlen l)) by lia.
      subst k. rewrite app_Znth2 by lia. rewrite Z.sub_diag. simpl. exact Hrange.
    - rewrite app_Znth1 by lia. apply Hn. lia.
    - change (0 <= k < Zlength (token_prefix_z i tlen l) + 1) in Hk.
      assert (Hkeq : k = Zlength (token_prefix_z i tlen l)) by lia.
      subst k. rewrite app_Znth2 by lia. rewrite Z.sub_diag. simpl. rewrite Hzi.
      unfold valid_string, no_inner_nul in PreH11.
      destruct PreH11 as [_ Hnul]. apply Hnul. lia. }
  Exists cnts_2.
  entailer!.
  - rewrite <- Hprefix. cancel.
  - unfold string_length. rewrite Hprefix, Zlength_app, PreH35. simpl.
    change (tlen + 1 < INT_MAX). lia.
  - unfold string_length. rewrite Hprefix, Zlength_app, PreH35. simpl.
    change (tlen + 1 = tlen + 1). reflexivity.
  - rewrite Hprefix, Zlength_app, PreH35. simpl.
    change (tlen + 1 = tlen + 1). reflexivity.
Qed.

Lemma proof_of_sort_numbers_entail_wit_11_6 : sort_numbers_entail_wit_11_6.
Proof.
  pre_process_default.
  assert (Htlen : tlen = 31) by lia. subst tlen.
  assert (Hzi : Znth i (l +:: 0) 0 = Znth i l 0).
  { rewrite app_Znth1 by lia. reflexivity. }
  assert (Hchar : scan_char_z i l = Znth i l 0).
  { unfold scan_char_z.
    assert (Hb : Z.ltb i (Zlength l) = true) by
      (apply Z.ltb_lt; lia).
    rewrite Hb. reflexivity. }
  assert (Hnon : scan_char_z i l <> 32).
  { rewrite Hchar, <- Hzi. exact PreH2. }
  assert (Hstart : scan_word_start_z (i + 1) l = scan_word_start_z i l).
  { rewrite scan_word_start_succ_19 by lia.
    destruct (Z.eqb_spec (scan_char_z i l) 32); [contradiction | reflexivity]. }
  assert (Hprefix : token_prefix_z (i + 1) 31 l = token_prefix_z i 31 l).
  { unfold token_prefix_z. simpl. rewrite Hstart. reflexivity. }
  assert (Hcompleted :
    scan_completed_prefix_z (i + 1) 31 l =
      scan_completed_prefix_z i 31 l).
  { unfold scan_completed_prefix_z. simpl. rewrite Hstart. reflexivity. }
  assert (Hcounts := scan_counts_advance_19 i l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0) ltac:(lia) PreH41).
  assert (Hexact : scan_counts_exact_z (i + 1) 31 l
    (Znth 0 cnts_2 0) (Znth 1 cnts_2 0) (Znth 2 cnts_2 0)
    (Znth 3 cnts_2 0) (Znth 4 cnts_2 0) (Znth 5 cnts_2 0)
    (Znth 6 cnts_2 0) (Znth 7 cnts_2 0) (Znth 8 cnts_2 0)
    (Znth 9 cnts_2 0)).
  { unfold scan_counts_exact_z in PreH42 |- *.
    rewrite Hcompleted. exact PreH42. }
  assert (Hsat : token_sat_start_z (i + 1) 31 l).
  { unfold token_sat_start_z in PreH40 |- *. intros.
    rewrite Hstart. specialize (PreH40 ltac:(lia)). lia. }
  assert (Hrange : 0 <= Znth i (l +:: 0) 0 <= 127).
  { rewrite Hzi. apply PreH13. lia. }
  Exists cnts_2.
  entailer!.
  rewrite <- Hprefix. cancel.
  - unfold token_empty_start_z. intros. lia.
  - rewrite Hprefix. exact PreH37.
  - rewrite Hprefix. exact PreH36.
  - rewrite Hprefix. exact PreH35.
  - rewrite Hprefix. exact PreH34.
Qed.

Lemma proof_of_sort_numbers_entail_wit_12 : sort_numbers_entail_wit_12.
Proof.
  pre_process_default.
  assert (Hi : i = len + 1) by lia. subst i.
  assert (Hchar_end : scan_char_z len l = 32).
  { unfold scan_char_z.
    assert (Hb : Z.ltb len (Zlength l) = false) by
      (apply Z.ltb_ge; lia).
    rewrite Hb. reflexivity. }
  assert (Hstart_end : scan_word_start_z (len + 1) l = len + 1).
  { rewrite scan_word_start_succ_19 by lia.
    rewrite Hchar_end. reflexivity. }
  assert (Htlen : tlen = 0).
  { destruct (Z_lt_dec tlen 31) as [Hlt | Hge].
    - assert (Hu := PreH37 Hlt).
      unfold token_unsat_end_z in Hu.
      destruct Hu; [assumption |]. rewrite Hstart_end in H. lia.
    - unfold token_sat_start_z in PreH38.
      specialize (PreH38 ltac:(lia)). rewrite Hstart_end in PreH38. lia. }
  subst tlen.
  assert (Hword0 := number_word_properties_19 0 ltac:(lia)).
  assert (Hc0 : 0 <= Znth 0 cnts_2 0).
  { unfold scan_counts_z in PreH39.
    repeat match goal with H : _ /\ _ |- _ => destruct H end. lia. }
  assert (Hcap :
    1 + Znth 0 cnts_2 0 * (number_word_len_z 0 + 1) <= INT_MAX).
  { unfold scan_counts_z, scan_counts_capacity_z in PreH39.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    unfold number_word_len_z in *. simpl in *. lia. }
  Exists cnts_2.
  entailer!.
  subst j. cancel.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_1 : sort_numbers_entail_wit_14_1.
Proof.
  pre_process_default.
  assert (Hi : i = 9) by lia. subst i.
  simpl in PreH13. subst word_ptr.
  Exists cnts_2.
  entailer!.
  unfold number_words_full, number_words_missing,
    number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_ptrs_z,
    number_word_len_z, number_word_z, store_string, c_string in *.
  sep_apply (PtrArray.full_split_to_missing_i (&( "words")) 9 10
    ((&( "w0")) :: (&( "w1")) :: (&( "w2")) :: (&( "w3")) ::
     (&( "w4")) :: (&( "w5")) :: (&( "w6")) :: (&( "w7")) ::
     (&( "w8")) :: (&( "w9")) :: nil) 0 ltac:(lia)).
  replace (sizeof(PTR)) with 4 in * by reflexivity.
  replace (sizeof(CHAR)) with 1 in * by reflexivity.
  entailer!.
  - unfold Znth, string_length. rewrite Zlength_correct. simpl. cancel.
    replace ((&( "w9")) + 0) with (&( "w9")) by lia.
    rewrite logic_equiv_sepcon_swap.
    cancel.
    apply derivable1_refl.
  - unfold Znth. simpl. lia.
Qed.

Ltac solve_sort_numbers_14_case_19 :=
  pre_process_default;
  repeat match goal with
  | H : ?x = ?rhs |- _ => is_var x; subst x
  end;
  simpl in *;
  match goal with
  | |- context [IntArray.full ?base 10 ?cs] => Exists cs
  end;
  (entailer!; try solve [unfold Znth; simpl; lia]);
  unfold number_words_full, number_words_missing,
    number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_ptrs_z,
    number_word_len_z, number_word_z, store_string, c_string in *;
  match goal with
  | |- context [PtrArray.missing_i ?base ?n 0 10 ?ls] =>
      sep_apply (PtrArray.full_split_to_missing_i
        base n 10 ls 0 ltac:(lia))
  end;
  replace (sizeof(PTR)) with 4 in * by reflexivity;
  replace (sizeof(CHAR)) with 1 in * by reflexivity;
  (entailer!; try solve [unfold Znth; simpl; lia]);
  unfold Znth, string_length; rewrite Zlength_correct; simpl; cancel;
  repeat match goal with
  | |- context [?wp + 0] => replace (wp + 0) with wp by lia
  end;
  try rewrite logic_equiv_sepcon_swap; cancel.

Lemma proof_of_sort_numbers_entail_wit_14_10 : sort_numbers_entail_wit_14_10.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_2 : sort_numbers_entail_wit_14_2.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_3 : sort_numbers_entail_wit_14_3.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_4 : sort_numbers_entail_wit_14_4.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_5 : sort_numbers_entail_wit_14_5.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_6 : sort_numbers_entail_wit_14_6.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_7 : sort_numbers_entail_wit_14_7.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_8 : sort_numbers_entail_wit_14_8.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_14_9 : sort_numbers_entail_wit_14_9.
Proof.
  solve_sort_numbers_14_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_15 : sort_numbers_entail_wit_15.
Proof.
  pre_process_default.
  subst retval word.
  assert (Hcompleted : scan_completed_prefix_z (len + 1) 0 l = l).
  { unfold scan_completed_prefix_z. simpl.
    replace (len + 1 - 0) with (len + 1) by lia.
    replace (Z.min (len + 1) (Zlength l)) with (Zlength l) by lia.
    apply sublist_self. reflexivity. }
  unfold scan_counts_exact_z in PreH20.
  rewrite Hcompleted in PreH20.
  assert (Hnextword : 0 <= i + 1 < 10 ->
    valid_string (number_word_z (i + 1)) /\
    string_length (number_word_z (i + 1)) = number_word_len_z (i + 1) /\
    string_length (number_word_z (i + 1)) < INT_MAX).
  { intro Hi. apply number_word_properties_19. exact Hi. }
  assert (HoutEq :
    out_len + Znth i cnts_2 0 * (number_word_len_z i + 1) =
      output_capacity_prefix_by_input_z (i + 1) l).
  { unfold output_capacity_prefix_by_input_z, output_capacity_prefix_z in *.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct_digit_cases_19 i; unfold number_word_len_z in *;
      simpl in *; try lia.
    change (out_len + Znth 0 cnts_2 0 * 5 =
      1 + count_word_in_string 0 l * 5).
    lia. }
  assert (Hnextnonneg : 0 <= Znth (i + 1) cnts_2 0).
  { unfold scan_counts_z in PreH19.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    destruct_digit_cases_19 i; simpl in *; try lia.
    assert (Hlen : List.length cnts_2 = 10%nat).
    { apply Nat2Z.inj. rewrite Zlength_correct in PreH18.
      simpl. exact PreH18. }
    unfold Znth; simpl; rewrite nth_overflow; lia. }
  assert (Hcnt10 : Znth 10 cnts_2 0 = 0).
  { assert (Hlen : List.length cnts_2 = 10%nat).
    { apply Nat2Z.inj. rewrite Zlength_correct in PreH18.
      simpl. exact PreH18. }
    unfold Znth. simpl. rewrite nth_overflow; lia. }
  assert (HC0 : 0 <= Znth 0 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC1 : 0 <= Znth 1 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC2 : 0 <= Znth 2 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC3 : 0 <= Znth 3 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC4 : 0 <= Znth 4 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC5 : 0 <= Znth 5 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC6 : 0 <= Znth 6 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC7 : 0 <= Znth 7 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC8 : 0 <= Znth 8 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  assert (HC9 : 0 <= Znth 9 cnts_2 0) by
    (unfold scan_counts_z in PreH19; tauto).
  destruct PreH20 as
    [HE0 [HE1 [HE2 [HE3 [HE4 [HE5 [HE6 [HE7 [HE8 HE9]]]]]]]]].
  assert (Hcapnext :
    out_len + Znth i cnts_2 0 * (number_word_len_z i + 1) +
      Znth (i + 1) cnts_2 0 * (number_word_len_z (i + 1) + 1) <=
      INT_MAX).
  { rewrite HoutEq.
    unfold scan_counts_z, scan_counts_capacity_z in PreH19.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    assert (Htotal :
      1 + Znth 0 cnts_2 0 * 5 + Znth 1 cnts_2 0 * 4 +
      Znth 2 cnts_2 0 * 4 + Znth 3 cnts_2 0 * 6 +
      Znth 4 cnts_2 0 * 5 + Znth 5 cnts_2 0 * 5 +
      Znth 6 cnts_2 0 * 4 + Znth 7 cnts_2 0 * 6 +
      Znth 8 cnts_2 0 * 6 + Znth 9 cnts_2 0 * 5 <= INT_MAX).
    { unfold number_word_len_z in *. simpl in *. nia. }
    unfold output_capacity_prefix_by_input_z, output_capacity_prefix_z in PreH27 |- *.
    rewrite <- HE0, <- HE1, <- HE2, <- HE3, <- HE4,
      <- HE5, <- HE6, <- HE7, <- HE8, <- HE9.
    destruct_digit_cases_19 i; unfold number_word_len_z in *;
      simpl in *; rewrite ?Hcnt10.
    all: lazymatch type of Htotal with ?mid <= _ =>
      eapply Z.le_trans with (m := mid); [nia | exact Htotal]
    end. }
  assert (Hwordlenbounds :
    -2147483648 <= number_word_len_z (i + 1) + 1 <= 2147483647).
  { destruct_digit_cases_19 i;
      unfold number_word_len_z, number_word_z in *; simpl in *; lia. }
  Exists cnts_2.
  entailer!.
  unfold number_words_full, number_words_missing,
    number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_ptrs_z,
    number_word_len_z, number_word_z, store_string, c_string in *.
  destruct_digit_cases_19 i; simpl in *; entailer!.
  all: try (
    eapply derivable1_trans;
    [ apply derivable1_sepcon_mono;
      [ cbn [Znth]; exact (derivable1_refl _)
      | match goal with
        | |- context [PtrArray.missing_i ?x ?n 0 ?m ?ls] =>
            apply (PtrArray.missing_i_merge_to_full
              x n m (Znth n ls 0) ls); lia
        end ]
    | rewrite replace_Znth_Znth by lia;
      cbn [Znth]; exact (derivable1_refl _) ]).
  all: try exact Hnextword.
  all: try (
    unfold scan_counts_exact_z;
    rewrite Hcompleted;
    repeat split; assumption).
  all: try (intro Hi; specialize (Hnextword Hi); tauto).
  all: try lia.
Qed.

Lemma proof_of_sort_numbers_entail_wit_16_1 : sort_numbers_entail_wit_16_1.
Proof.
  pre_process_default.
  assert (Hi : i = 10) by lia.
  subst i.
  assert (Hprefix : output_prefix_by_input_z 0 0 l = nil).
  { change (append_repeated_number_word_z (@nil Z) 0
      (count_word_in_string 0 l) 0 = nil).
    unfold append_repeated_number_word_z.
    reflexivity. }
  assert (Hused :
    out_len - 1 = output_used_capacity_prefix_by_input_z 10 l).
  { unfold output_used_capacity_prefix_by_input_z,
      output_used_capacity_prefix_z.
    fold (output_capacity_prefix_by_input_z 10 l).
    rewrite <- PreH25.
    destruct (Z.leb out_len 1) eqn:Hle.
    - apply Z.leb_le in Hle. lia.
    - reflexivity. }
  Exists cnts_2.
  rewrite Hprefix.
  entailer!.
  unfold CharArray.full, store_array.
  simpl.
  cancel.
  all: try (change (1 <= out_len - 1); lia).
  all: entailer!; cancel.
Qed.

Lemma proof_of_sort_numbers_entail_wit_16_2 : sort_numbers_entail_wit_16_2.
Proof.
  pre_process_default.
  assert (Hi : i = 10) by lia.
  subst i.
  assert (Hout : out_len = 1) by lia.
  assert (Hprefix : output_prefix_by_input_z 0 0 l = nil).
  { change (append_repeated_number_word_z (@nil Z) 0
      (count_word_in_string 0 l) 0 = nil).
    unfold append_repeated_number_word_z.
    reflexivity. }
  assert (Hused :
    out_len = output_used_capacity_prefix_by_input_z 10 l).
  { unfold output_used_capacity_prefix_by_input_z,
      output_used_capacity_prefix_z.
    fold (output_capacity_prefix_by_input_z 10 l).
    rewrite <- PreH25.
    rewrite Hout.
    reflexivity. }
  rewrite Hout in *.
  Exists cnts_2.
  rewrite Hprefix.
  entailer!.
  unfold CharArray.full, store_array, CharArray.undef_seg,
    store_undef_array.
  simpl.
  cancel.
  all: entailer!; cancel.
Qed.

Lemma proof_of_sort_numbers_entail_wit_17 : sort_numbers_entail_wit_17.
Proof.
  pre_process_default.
  pose proof (number_word_properties_19 i ltac:(lia)) as Hword.
  destruct Hword as [Hvalid [Hlen Hmax]].
  Exists cnts_2
    (Znth i
      ((&( "w0")) :: (&( "w1")) :: (&( "w2")) :: (&( "w3")) ::
       (&( "w4")) :: (&( "w5")) :: (&( "w6")) :: (&( "w7")) ::
       (&( "w8")) :: (&( "w9")) :: nil) 0).
  entailer!.
Qed.

Lemma printable_number_word_19 :
  forall d, 0 <= d < 10 ->
    Forall (fun x => 1 <= x <= 127) (number_word_z d).
Proof.
  intros d Hd.
  destruct_digit_cases_19 d;
    unfold number_word_z; simpl; repeat constructor; lia.
Qed.

Lemma printable_append_number_word_19 :
  forall prefix d,
    Forall (fun x => 1 <= x <= 127) prefix ->
    0 <= d < 10 ->
    Forall (fun x => 1 <= x <= 127)
      (append_number_word_z prefix d).
Proof.
  intros prefix d Hprefix Hd.
  unfold append_number_word_z.
  apply Forall_app. split; [exact Hprefix |].
  apply Forall_app. split.
  - destruct (Z.eqb (Zlength prefix) 0); simpl;
      constructor; try lia; constructor.
  - apply printable_number_word_19. exact Hd.
Qed.

Lemma printable_append_repeated_number_word_nat_19 :
  forall prefix d n,
    Forall (fun x => 1 <= x <= 127) prefix ->
    0 <= d < 10 ->
    Forall (fun x => 1 <= x <= 127)
      (append_repeated_number_word_nat prefix d n).
Proof.
  intros prefix d n Hprefix Hd.
  induction n; simpl; [exact Hprefix |].
  apply printable_append_number_word_19; assumption.
Qed.

Lemma printable_output_prefix_by_input_19 :
  forall d done input, 0 <= d < 10 ->
    Forall (fun x => 1 <= x <= 127)
      (output_prefix_by_input_z d done input).
Proof.
  intros d done input Hd.
  unfold output_prefix_by_input_z, output_prefix_z,
    append_repeated_number_word_z.
  destruct_digit_cases_19 d.
  all: repeat (apply printable_append_repeated_number_word_nat_19;
    [| lia]).
  all: constructor.
Qed.

Lemma printable_valid_string_19 :
  forall s, Forall (fun x => 1 <= x <= 127) s -> valid_string s.
Proof.
  intros s Hs.
  unfold valid_string, all_ascii, no_inner_nul.
  split; intros i Hi.
  - assert (Hnat : (Z.to_nat i < List.length s)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      lia. }
    pose proof
      ((proj1 (Forall_nth (fun x : Z => 1 <= x <= 127) s))
        Hs (Z.to_nat i) 0 Hnat) as Hnth.
    unfold Znth. destruct Hnth. lia.
  - assert (Hnat : (Z.to_nat i < List.length s)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct.
      lia. }
    pose proof
      ((proj1 (Forall_nth (fun x : Z => 1 <= x <= 127) s))
        Hs (Z.to_nat i) 0 Hnat) as Hnth.
    unfold Znth. destruct Hnth. lia.
Qed.

Lemma output_prefix_valid_string_19 :
  forall d done input, 0 <= d < 10 ->
    valid_string (output_prefix_by_input_z d done input).
Proof.
  intros. apply printable_valid_string_19.
  apply printable_output_prefix_by_input_19. assumption.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_1 : sort_numbers_entail_wit_18_1.
Proof.
  pre_process_default.
  subst i word_ptr.
  assert (Hprefix : output_prefix_by_input_z 0 0 l = nil).
  { change (append_repeated_number_word_z (@nil Z) 0
      (count_word_in_string 0 l) 0 = nil).
    unfold append_repeated_number_word_z.
    reflexivity. }
  assert (H10valid : valid_string (number_word_z 10)).
  { unfold valid_string, all_ascii, no_inner_nul, number_word_z.
    split; intros k Hk;
      assert (k = 0) by
        (rewrite Zlength_correct in Hk; simpl in Hk; lia);
      subst k; unfold Znth; simpl; lia. }
  assert (H10len :
    string_length (number_word_z 10) = number_word_len_z 10).
  { reflexivity. }
  assert (H10max : string_length (number_word_z 10) < INT_MAX).
  { unfold string_length, number_word_z.
    rewrite Zlength_correct. simpl. lia. }
  assert (Hnilvalid : valid_string nil).
  { unfold valid_string, all_ascii, no_inner_nul.
    split; intros k Hk;
      rewrite Zlength_correct in Hk; simpl in Hk; lia. }
  assert (Hcnt0 : 0 <= Znth 0 cnts_2 0).
  { unfold scan_counts_z in PreH18. tauto. }
  Exists cnts_2.
  rewrite Hprefix in *.
  entailer!.
  unfold number_words_full, number_words_missing,
    number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_ptrs_z,
    number_word_len_z, number_word_z, store_string, c_string in *.
  sep_apply (PtrArray.full_split_to_missing_i
    (&( "words")) 0 10
    ((&( "w0")) :: (&( "w1")) :: (&( "w2")) :: (&( "w3")) ::
     (&( "w4")) :: (&( "w5")) :: (&( "w6")) :: (&( "w7")) ::
     (&( "w8")) :: (&( "w9")) :: nil) 0 ltac:(lia)).
  replace (sizeof(PTR)) with 4 in * by reflexivity.
  replace (sizeof(CHAR)) with 1 in * by reflexivity.
  simpl in *.
  entailer!.
  unfold Znth in *.
  simpl in *.
  cancel.
  repeat match goal with
  | |- context [?x + 0] => replace (x + 0) with x by lia
  end.
  cancel.
  exact (derivable1_refl _).
Qed.

Lemma number_word_10_properties_19 :
  valid_string (number_word_z 10) /\
  string_length (number_word_z 10) = number_word_len_z 10 /\
  string_length (number_word_z 10) < INT_MAX.
Proof.
  split.
  - unfold valid_string, all_ascii, no_inner_nul, number_word_z.
    split; intros k Hk;
      assert (k = 0) by
        (rewrite Zlength_correct in Hk; simpl in Hk; lia);
      subst k; unfold Znth; simpl; lia.
  - split; [reflexivity |].
    unfold string_length, number_word_z.
    rewrite Zlength_correct. simpl. lia.
Qed.

Ltac solve_sort_numbers_18_case_19 :=
  pre_process_default;
  match goal with
  | |- context [valid_string (output_prefix_by_input_z ?d 0 ?inp)] =>
      let Hprefix := fresh "Hprefix" in
      assert (Hprefix :
        valid_string (output_prefix_by_input_z d 0 inp)) by
          (apply output_prefix_valid_string_19; lia)
  end;
  let H10 := fresh "H10" in
  pose proof number_word_10_properties_19 as H10;
  destruct H10 as [? [? ?]];
  match goal with
  | Hscan : scan_counts_z _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold scan_counts_z in Hscan;
      repeat match type of Hscan with
      | _ /\ _ => destruct Hscan
      end
  end;
  match goal with
  | |- context [IntArray.full ?base 10 ?cs] => Exists cs
  end;
  entailer!;
  simpl in *;
  unfold number_words_full, number_words_missing,
    number_word_ptrs_z in *;
  match goal with
  | |- (?chars ** PtrArray.full ?base 10 ?ls) |-- ?R =>
      match goal with
      | |- context [PtrArray.missing_i base ?n 0 10 ls] =>
          eapply derivable1_trans with
            (y := PtrArray.full base 10 ls ** chars);
          [ rewrite logic_equiv_sepcon_comm;
            exact (derivable1_refl _)
          | eapply derivable1_trans;
            [ apply derivable1_sepcon_mono;
              [ apply (PtrArray.full_split_to_missing_i
                  base n 10 ls 0 ltac:(lia))
              | exact (derivable1_refl _) ]
            | ] ]
      end
  end;
  unfold number_words_chars_full_z, number_words_chars_missing_z,
    number_word_char_full_z, number_word_len_z, number_word_z,
    store_string, c_string in *;
  replace (sizeof(PTR)) with 4 in * by reflexivity;
  replace (sizeof(CHAR)) with 1 in * by reflexivity;
  simpl in *;
  entailer!;
  unfold Znth in *; simpl in *;
  repeat match goal with
  | |- context [?x + 0] => replace (x + 0) with x by lia
  end;
  cancel;
  try exact (derivable1_refl _).

Lemma proof_of_sort_numbers_entail_wit_18_10 : sort_numbers_entail_wit_18_10.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_2 : sort_numbers_entail_wit_18_2.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_3 : sort_numbers_entail_wit_18_3.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_4 : sort_numbers_entail_wit_18_4.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_5 : sort_numbers_entail_wit_18_5.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_6 : sort_numbers_entail_wit_18_6.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_7 : sort_numbers_entail_wit_18_7.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_8 : sort_numbers_entail_wit_18_8.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_18_9 : sort_numbers_entail_wit_18_9.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_19 : sort_numbers_entail_wit_19.
Proof.
  solve_sort_numbers_18_case_19.
Qed.

Lemma proof_of_sort_numbers_entail_wit_2 : sort_numbers_entail_wit_2.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_20 : sort_numbers_entail_wit_20.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_21 : sort_numbers_entail_wit_21.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_22_1 : sort_numbers_entail_wit_22_1.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_22_2 : sort_numbers_entail_wit_22_2.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_23 : sort_numbers_entail_wit_23.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_24 : sort_numbers_entail_wit_24.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_3 : sort_numbers_entail_wit_3.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_4 : sort_numbers_entail_wit_4.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_5 : sort_numbers_entail_wit_5.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_6 : sort_numbers_entail_wit_6.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_7_1 : sort_numbers_entail_wit_7_1.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_7_2 : sort_numbers_entail_wit_7_2.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_8 : sort_numbers_entail_wit_8.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_1 : sort_numbers_entail_wit_9_1.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_10 : sort_numbers_entail_wit_9_10.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_2 : sort_numbers_entail_wit_9_2.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_3 : sort_numbers_entail_wit_9_3.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_4 : sort_numbers_entail_wit_9_4.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_5 : sort_numbers_entail_wit_9_5.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_6 : sort_numbers_entail_wit_9_6.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_7 : sort_numbers_entail_wit_9_7.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_8 : sort_numbers_entail_wit_9_8.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_entail_wit_9_9 : sort_numbers_entail_wit_9_9.
Proof.
  pre_process_default.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_return_wit_1 : sort_numbers_return_wit_1.
Proof.
  pre_process_default.
  entailer!.
Qed.


Lemma proof_of_sort_numbers_safety_wit_217 : sort_numbers_safety_wit_217.
Proof.
  left.
  intros.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_safety_wit_218 : sort_numbers_safety_wit_218.
Proof.
  left.
  intros.
  entailer!.
Qed.

Lemma proof_of_sort_numbers_safety_wit_266 : sort_numbers_safety_wit_266.
Proof.
  left.
  intros.
  unfold scan_counts_z in PreH19.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  destruct_digit_cases_19 i; entailer!; lia.
Qed.

Lemma proof_of_sort_numbers_safety_wit_267 : sort_numbers_safety_wit_267.
Proof.
  left.
  intros.
  unfold scan_counts_z in PreH19.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  destruct_digit_cases_19 i; entailer!; lia.
Qed.
