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
From SimpleC.EE.CAV.ground_truth_p111_histogram Require Import p111_histogram_goal.
From SimpleC.EE.CAV.ground_truth_p111_histogram Require Import p111_histogram_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import p111_histogram.
Local Open Scope sac.
Import ListNotations.

Definition byte_range_111 (z : Z) : Prop := 0 <= z < 256.

Lemma Forall_byte_range_of_Znth_111 : forall l,
  (forall k : Z, 0 <= k < Zlength l -> byte_range_111 (Znth k l 0)) ->
  Forall byte_range_111 l.
Proof.
  induction l as [|a l IH]; intros Hrange; constructor.
  - specialize (Hrange 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia)).
    rewrite Znth0_cons in Hrange. exact Hrange.
  - apply IH. intros k Hk.
    specialize (Hrange (k + 1)
      ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg l); lia)).
    rewrite Znth_cons in Hrange by lia.
    replace (k + 1 - 1) with k in Hrange by lia. exact Hrange.
Qed.

Lemma ascii_of_z_inj_111 : forall x y,
  byte_range_111 x -> byte_range_111 y ->
  ascii_of_z_111 x = ascii_of_z_111 y -> x = y.
Proof.
  intros x y Hx Hy Heq. unfold byte_range_111 in Hx, Hy.
  unfold ascii_of_z_111 in Heq.
  apply (f_equal nat_of_ascii) in Heq.
  rewrite !nat_ascii_embedding in Heq by lia.
  now apply Z2Nat.inj.
Qed.

Lemma ascii_of_z_space_111 : forall z,
  byte_range_111 z ->
  (ascii_of_z_111 z = " "%char <-> z = 32).
Proof.
  intros z Hz. unfold byte_range_111 in Hz. split; intros H.
  - apply (f_equal nat_of_ascii) in H.
    unfold ascii_of_z_111 in H.
    rewrite nat_ascii_embedding in H by lia.
    assert (Hz32 : z = 32) by (apply Z2Nat.inj; try lia; exact H).
    exact Hz32.
  - subst z. reflexivity.
Qed.

Lemma list_ascii_string_of_list_z_111 : forall l,
  list_ascii_of_string (string_of_list_z_111 l) = map ascii_of_z_111 l.
Proof. induction l; simpl; congruence. Qed.

Lemma filter_spaces_map_111 : forall l,
  Forall byte_range_111 l ->
  filter_spaces (map ascii_of_z_111 l) =
  map ascii_of_z_111 (filter non_space_111 l).
Proof.
  intros l Hl. induction Hl as [|z l Hz Hl IH].
  - reflexivity.
  - unfold filter_spaces in *. simpl.
    destruct (ascii_dec (ascii_of_z_111 z) " "%char) as [Heq|Hneq].
    + apply ascii_of_z_space_111 in Heq; [|exact Hz]. subst z.
      simpl. exact IH.
    + assert (Hz32 : z <> 32).
      { intro Heq. subst z. apply Hneq. reflexivity. }
      assert (Hzb : (z =? 32)%Z = false) by (apply Z.eqb_neq; exact Hz32).
      unfold non_space_111. rewrite Hzb. simpl. now rewrite IH.
Qed.

Lemma prefix_letters_full_111 : forall input,
  prefix_letters_111 input (Zlength input) = filter non_space_111 input.
Proof.
  intros input. unfold prefix_letters_111.
  rewrite Zlength_correct, Nat2Z.id, firstn_all. reflexivity.
Qed.

Lemma count_ascii_map_111 : forall l z,
  Forall byte_range_111 l -> byte_range_111 z ->
  count_char (map ascii_of_z_111 l) (ascii_of_z_111 z) =
  count_occ Z.eq_dec l z.
Proof.
  intros l z Hl Hz. induction Hl as [|x l Hx Hl IH]; simpl; [reflexivity|].
  destruct (Z.eq_dec x z) as [->|Hneq].
  - destruct (ascii_dec (ascii_of_z_111 z) (ascii_of_z_111 z));
      [simpl; now rewrite IH|contradiction].
  - assert (Hascii : ascii_of_z_111 x <> ascii_of_z_111 z).
    { intro H. apply ascii_of_z_inj_111 in H; auto. }
    destruct (ascii_dec (ascii_of_z_111 x) (ascii_of_z_111 z));
      [contradiction|].
    destruct (Z.eq_dec x z); [contradiction|exact IH].
Qed.

Lemma fold_nat_max_upper_111 : forall xs n,
  In n xs -> (n <= fold_right Nat.max 0 xs)%nat.
Proof.
  induction xs as [|x xs IH]; intros n Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

Lemma fold_nat_max_le_111 : forall xs b,
  (forall n, In n xs -> (n <= b)%nat) ->
  (fold_right Nat.max 0 xs <= b)%nat.
Proof.
  induction xs as [|x xs IH]; intros b Hb; simpl.
  - lia.
  - apply Nat.max_lub; [apply Hb; left; reflexivity|].
    apply IH. intros n Hin. apply Hb. right. exact Hin.
Qed.

Lemma fold_Zmax_upper_111 : forall xs n,
  In n xs -> n <= fold_right Z.max 0 xs.
Proof.
  induction xs as [|x xs IH]; intros n Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + apply Z.le_max_l.
    + eapply Z.le_trans; [apply IH; exact Hin|apply Z.le_max_r].
Qed.

Lemma fold_Zmax_le_111 : forall xs b,
  0 <= b -> (forall n, In n xs -> n <= b) ->
  fold_right Z.max 0 xs <= b.
Proof.
  induction xs as [|x xs IH]; intros b Hb0 Hb; simpl.
  - exact Hb0.
  - apply Z.max_lub; [apply Hb; left; reflexivity|].
    apply IH; [exact Hb0|]. intros n Hin. apply Hb. right. exact Hin.
Qed.

Lemma get_max_count_upper_111 : forall letters c,
  In c letters -> (count_char letters c <= get_max_count letters)%nat.
Proof.
  intros letters c Hin. unfold get_max_count.
  apply fold_nat_max_upper_111. apply in_map.
  apply nodup_In. exact Hin.
Qed.

Lemma get_max_count_le_111 : forall letters b,
  (forall c, In c letters -> (count_char letters c <= b)%nat) ->
  (get_max_count letters <= b)%nat.
Proof.
  intros letters b Hb. unfold get_max_count. apply fold_nat_max_le_111.
  intros n Hn. apply in_map_iff in Hn.
  destruct Hn as [c [<- Hc]]. apply Hb. apply nodup_In in Hc. exact Hc.
Qed.

Lemma In_byte_domain_111 : forall z,
  In z byte_domain_111 <-> 0 <= z < 256.
Proof.
  intros z. unfold byte_domain_111. rewrite in_map_iff. split.
  - intros [n [<- Hn]]. apply in_seq in Hn. lia.
  - intros Hz. exists (Z.to_nat z). split.
    + rewrite Z2Nat.id by lia. reflexivity.
    + apply in_seq. lia.
Qed.

Lemma selected_keys_In_111 : forall counts max z,
  In z (selected_keys_111 counts max 256) <->
  0 <= z < 256 /\ Znth z counts 0 = max /\ 0 < max.
Proof.
  intros counts max z. unfold selected_keys_111.
  rewrite filter_In. split.
  - intros [Hdom Htest]. apply in_map_iff in Hdom.
    destruct Hdom as [n [<- Hn]]. apply in_seq in Hn.
    apply andb_true_iff in Htest. destruct Htest as [Hcount Hmax].
    apply Z.eqb_eq in Hcount. apply Z.ltb_lt in Hmax. lia.
  - intros [Hz [Hcount Hmax]]. split.
    + apply in_map_iff. exists (Z.to_nat z). split.
      * rewrite Z2Nat.id by lia. reflexivity.
      * apply in_seq. lia.
    + apply andb_true_iff. split; [apply Z.eqb_eq|apply Z.ltb_lt]; assumption.
Qed.

Lemma zip_histogram_map_In_111 : forall keys f p,
  In p (zip_histogram_111 keys (map f keys)) <->
  exists k, In k keys /\ p = (ascii_of_z_111 k, Z.to_nat (f k)).
Proof.
  induction keys as [|k keys IH]; intros f p; simpl.
  - split; [contradiction|intros [x [H _]]; contradiction].
  - rewrite IH. split.
    + intros [Hp|Hp].
      * exists k. split; [left; reflexivity|symmetry; exact Hp].
      * destruct Hp as [x [Hx Hp]]. exists x. split; [right; exact Hx|exact Hp].
    + intros [x [[Hx|Hx] Hp]].
      * subst x. left. symmetry. exact Hp.
      * right. exists x. split; assumption.
Qed.

Lemma Nat2Z_fold_max_111 : forall xs,
  Z.of_nat (fold_right Nat.max 0%nat xs) =
  fold_right Z.max 0 (map Z.of_nat xs).
Proof.
  induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite Nat2Z.inj_max, IH. reflexivity.
Qed.

Lemma nodup_eq_nil_111 : forall (A : Type)
    (dec : forall x y : A, {x = y} + {x <> y}) (xs : list A),
  nodup dec xs = [] -> xs = [].
Proof.
  intros A dec xs. induction xs as [|x xs IH]; intros H; [reflexivity|].
  simpl in H. destruct (in_dec dec x xs) as [Hin|Hnin].
  - apply IH in H. subst xs. contradiction.
  - discriminate.
Qed.

Lemma max_counts_at_full_111 : forall input,
  Forall byte_range_111 input ->
  max_count_z_111 (counts_at_111 input (Zlength input)) =
  Z.of_nat (get_max_count
    (map ascii_of_z_111 (filter non_space_111 input))).
Proof.
  intros input Hinput.
  assert (Hletters : Forall byte_range_111 (filter non_space_111 input)).
  { apply Forall_forall. intros z Hz. apply filter_In in Hz.
    eapply Forall_forall; [exact Hinput|exact (proj1 Hz)]. }
  apply Z.le_antisymm.
  - unfold max_count_z_111, counts_at_111. rewrite prefix_letters_full_111.
    apply fold_Zmax_le_111; [lia|]. intros n Hn.
    apply in_map_iff in Hn. destruct Hn as [z [<- Hz]].
    apply In_byte_domain_111 in Hz.
    unfold count_byte_111.
    destruct (count_occ Z.eq_dec (filter non_space_111 input) z) eqn:Hcount.
    + simpl. lia.
    + assert (Hin : In z (filter non_space_111 input)).
      { apply (proj2 (count_occ_In Z.eq_dec _ _)). rewrite Hcount. lia. }
      pose proof (get_max_count_upper_111
        (map ascii_of_z_111 (filter non_space_111 input))
        (ascii_of_z_111 z) (in_map _ _ _ Hin)) as Hupper.
      rewrite (count_ascii_map_111 _ z Hletters Hz) in Hupper.
      unfold count_char in Hupper. lia.
  - unfold get_max_count. rewrite Nat2Z_fold_max_111.
    apply fold_Zmax_le_111; [unfold max_count_z_111; induction (counts_at_111 input (Zlength input)); simpl; lia|].
    intros n Hn. apply in_map_iff in Hn.
    destruct Hn as [m [<- Hm]]. apply in_map_iff in Hm.
    destruct Hm as [c [<- Hc]]. apply nodup_In in Hc.
    apply in_map_iff in Hc. destruct Hc as [z [Hzc Hin]]. subst c.
    assert (Hz : byte_range_111 z).
    { eapply Forall_forall; [exact Hletters|exact Hin]. }
    rewrite count_ascii_map_111 by assumption.
    unfold count_char, count_byte_111, max_count_z_111.
    apply fold_Zmax_upper_111. unfold counts_at_111.
    rewrite prefix_letters_full_111. apply in_map_iff. exists z. split.
    + reflexivity.
    + apply In_byte_domain_111. exact Hz.
Qed.

Lemma counts_at_length_111 : forall input i,
  length (counts_at_111 input i) = 256%nat.
Proof.
  intros. unfold counts_at_111, byte_domain_111.
  rewrite !length_map, length_seq. reflexivity.
Qed.

Lemma nth_counts_at_111 : forall input i n,
  (n < 256)%nat ->
  nth n (counts_at_111 input i) 0 =
  count_byte_111 (prefix_letters_111 input i) (Z.of_nat n).
Proof.
  intros input i n Hn.
  rewrite (List.nth_indep (n := n) (counts_at_111 input i) 0
    (count_byte_111 (prefix_letters_111 input i) 0)).
  2: { rewrite counts_at_length_111. exact Hn. }
  unfold counts_at_111, byte_domain_111.
  rewrite map_nth with (d := 0%Z).
  rewrite map_nth with (d := 0%nat).
  rewrite seq_nth by exact Hn. simpl. reflexivity.
Qed.

Lemma Znth_counts_at_full_111 : forall input z,
  0 <= z < 256 ->
  Znth z (counts_at_111 input (Zlength input)) 0 =
  count_byte_111 (filter non_space_111 input) z.
Proof.
  intros input z Hz. unfold Znth.
  rewrite nth_counts_at_111 by lia. rewrite Z2Nat.id by lia.
  rewrite prefix_letters_full_111. reflexivity.
Qed.

Lemma selected_keys_empty_111 : forall input counts max,
  Forall byte_range_111 input ->
  counts = counts_at_111 input (Zlength input) ->
  max = max_count_z_111 counts ->
  nodup ascii_dec
    (map ascii_of_z_111 (filter non_space_111 input)) = [] ->
  selected_keys_111 counts max 256 = [].
Proof.
  intros input counts max Hinput Hcounts Hmax Hunique.
  assert (Hletters_nil : filter non_space_111 input = []).
  { apply (map_eq_nil ascii_of_z_111).
    apply (nodup_eq_nil_111 ascii ascii_dec). exact Hunique. }
  assert (Hmax_zero : max = 0).
  { rewrite Hmax, Hcounts, max_counts_at_full_111 by exact Hinput.
    rewrite Hletters_nil. reflexivity. }
  unfold selected_keys_111. rewrite Hmax_zero.
  transitivity (filter (fun _ : Z => false)
    (map Z.of_nat (seq 0 (Z.to_nat 256)))).
  - apply filter_ext_in. intros z _. rewrite Z.ltb_irrefl, andb_false_r.
    reflexivity.
  - induction (map Z.of_nat (seq 0 (Z.to_nat 256))); simpl; congruence.
Qed.

Local Opaque selected_keys_111 counts_at_111 max_count_z_111.

Lemma operational_sound_111 : forall input counts max (p : ascii * nat),
  Forall byte_range_111 input ->
  counts = counts_at_111 input (Zlength input) ->
  max = max_count_z_111 counts ->
  In p (zip_histogram_111 (selected_keys_111 counts max 256)
    (selected_values_111 counts max 256)) ->
  let (c, n) := p in
  n = get_max_count
      (map ascii_of_z_111 (filter non_space_111 input)) /\
  count_char (map ascii_of_z_111 (filter non_space_111 input)) c =
      get_max_count
        (map ascii_of_z_111 (filter non_space_111 input)).
Proof.
  intros input counts max [c n] Hinput Hcounts Hmax Hp. simpl.
  set (letters_z := filter non_space_111 input).
  set (letters := map ascii_of_z_111 letters_z).
  set (keys := selected_keys_111 counts max 256).
  assert (Hletters_z : Forall byte_range_111 letters_z).
  { unfold letters_z. apply Forall_forall. intros z Hz.
    apply filter_In in Hz. eapply Forall_forall; [exact Hinput|exact (proj1 Hz)]. }
  assert (Hmax_correct : max = Z.of_nat (get_max_count letters)).
  { rewrite Hmax, Hcounts. apply max_counts_at_full_111. exact Hinput. }
  unfold selected_values_111 in Hp. fold keys in Hp.
  apply zip_histogram_map_In_111 in Hp.
  destruct Hp as [z [Hz Hinpair]].
  unfold keys in Hz. apply selected_keys_In_111 in Hz.
  destruct Hz as [Hzrange [Hzcount _]].
  inversion Hinpair; subst c n; clear Hinpair.
  assert (Hcount_z : count_byte_111 letters_z z = max).
  { rewrite <- Hzcount, Hcounts. unfold letters_z.
    symmetry. apply Znth_counts_at_full_111. exact Hzrange. }
  assert (Hcount_ascii :
    count_char letters (ascii_of_z_111 z) = Z.to_nat max).
  { unfold letters. rewrite count_ascii_map_111 by assumption.
    unfold count_byte_111 in Hcount_z.
    apply (f_equal Z.to_nat) in Hcount_z.
    rewrite Nat2Z.id in Hcount_z. exact Hcount_z. }
  assert (Hmax_nat : Z.to_nat max = get_max_count letters).
  { rewrite Hmax_correct, Nat2Z.id. reflexivity. }
  fold letters. rewrite Hmax_nat in Hcount_ascii. split.
  - rewrite Hzcount. exact Hmax_nat.
  - exact Hcount_ascii.
Qed.

Lemma operational_complete_111 : forall input counts max c,
  Forall byte_range_111 input ->
  counts = counts_at_111 input (Zlength input) ->
  max = max_count_z_111 counts -> 0 < max ->
  In c (nodup ascii_dec
    (map ascii_of_z_111 (filter non_space_111 input))) ->
  count_char (map ascii_of_z_111 (filter non_space_111 input)) c =
    get_max_count (map ascii_of_z_111 (filter non_space_111 input)) ->
  In (c, get_max_count
      (map ascii_of_z_111 (filter non_space_111 input)))
    (zip_histogram_111 (selected_keys_111 counts max 256)
      (selected_values_111 counts max 256)).
Proof.
  intros input counts max c Hinput Hcounts Hmax Hmax_pos Hc Hcount.
  set (letters_z := filter non_space_111 input).
  set (letters := map ascii_of_z_111 letters_z).
  set (keys := selected_keys_111 counts max 256).
  assert (Hletters_z : Forall byte_range_111 letters_z).
  { unfold letters_z. apply Forall_forall. intros z Hz.
    apply filter_In in Hz. eapply Forall_forall; [exact Hinput|exact (proj1 Hz)]. }
  assert (Hmax_correct : max = Z.of_nat (get_max_count letters)).
  { rewrite Hmax, Hcounts. apply max_counts_at_full_111. exact Hinput. }
  apply (proj1 (nodup_In ascii_dec _ c)) in Hc.
  fold letters in Hc. apply in_map_iff in Hc.
  destruct Hc as [z [Hcz Hzletters]]. subst c.
  assert (Hzrange : byte_range_111 z).
  { eapply Forall_forall; [exact Hletters_z|exact Hzletters]. }
  assert (Hcount_z : count_byte_111 letters_z z = max).
  { fold letters in Hcount. unfold letters in Hcount.
    rewrite count_ascii_map_111 in Hcount by assumption.
    unfold count_char, count_byte_111 in *.
    rewrite Hmax_correct. exact (f_equal Z.of_nat Hcount). }
  unfold selected_values_111. fold keys.
  apply zip_histogram_map_In_111. exists z. split.
  - unfold keys. apply selected_keys_In_111. split; [exact Hzrange|].
    split; [|exact Hmax_pos]. rewrite Hcounts.
    rewrite Znth_counts_at_full_111 by exact Hzrange. exact Hcount_z.
  - f_equal. rewrite Hcounts, Znth_counts_at_full_111 by exact Hzrange.
    fold letters_z. fold letters.
    rewrite Hcount_z, Hmax_correct, Nat2Z.id. reflexivity.
Qed.

Lemma operational_problem_nonempty_111 : forall input counts max first rest,
  Forall byte_range_111 input ->
  counts = counts_at_111 input (Zlength input) ->
  max = max_count_z_111 counts ->
  nodup ascii_dec
    (map ascii_of_z_111 (filter non_space_111 input)) = first :: rest ->
  problem_111_spec (string_of_list_z_111 input)
    (zip_histogram_111 (selected_keys_111 counts max 256)
      (selected_values_111 counts max 256)).
Proof.
  intros input counts max first rest Hinput Hcounts Hmax Hunique.
  unfold problem_111_spec. rewrite list_ascii_string_of_list_z_111.
  rewrite filter_spaces_map_111 by exact Hinput. rewrite Hunique.
  assert (Hfirst : In first
      (map ascii_of_z_111 (filter non_space_111 input))).
  { apply (proj1 (nodup_In ascii_dec _ first)).
    rewrite Hunique. left. reflexivity. }
  assert (Hmax_nat_pos : (0 < get_max_count
      (map ascii_of_z_111 (filter non_space_111 input)))%nat).
  { eapply Nat.lt_le_trans.
    - apply (proj1 (count_occ_In ascii_dec
        (map ascii_of_z_111 (filter non_space_111 input)) first)).
      exact Hfirst.
    - apply get_max_count_upper_111. exact Hfirst. }
  assert (Hmax_correct : max = Z.of_nat (get_max_count
      (map ascii_of_z_111 (filter non_space_111 input)))).
  { rewrite Hmax, Hcounts. apply max_counts_at_full_111. exact Hinput. }
  assert (Hmax_pos : 0 < max) by (rewrite Hmax_correct; lia).
  split.
  - intros p Hp. eapply operational_sound_111; eauto.
  - intros c Hc Hcount.
    eapply operational_complete_111; eauto.
    rewrite Hunique. exact Hc.
Qed.

Lemma operational_spec_111 : forall input counts max keys values,
  Forall byte_range_111 input ->
  counts = counts_at_111 input (Zlength input) ->
  max = max_count_z_111 counts ->
  problem_111_output_prefix_z counts max 256 keys values ->
  problem_111_spec_z input keys values.
Proof.
  intros input counts max keys values Hinput Hcounts Hmax [Hkeys Hvalues].
  subst keys values. unfold selected_values_111.
  set (keys := selected_keys_111 counts max 256).
  split; [now rewrite length_map|]. split.
  - apply Forall_forall. intros v Hv. apply in_map_iff in Hv.
    destruct Hv as [z [<- Hz]]. unfold keys in Hz.
    apply selected_keys_In_111 in Hz. lia.
  - unfold keys. destruct (nodup ascii_dec
      (map ascii_of_z_111 (filter non_space_111 input)))
      as [|first rest] eqn:Hunique.
    + pose proof (selected_keys_empty_111 input counts max
        Hinput Hcounts Hmax Hunique) as Hempty.
      unfold problem_111_spec. rewrite list_ascii_string_of_list_z_111.
      rewrite filter_spaces_map_111 by exact Hinput.
      rewrite Hunique, Hempty. reflexivity.
    + apply operational_problem_nonempty_111 with (first := first) (rest := rest);
        assumption.
Qed.

Lemma package_histogram_result_111 : forall
    (P : Prop) test_pre input out keys values size
    key_list value_list,
  out <> 0 -> keys <> 0 -> values <> 0 ->
  0 <= size -> size <= 256 ->
  Zlength key_list = size -> Zlength value_list = size -> P ->
  (&( out # "<anonymous struct>" ->ₛ "keys") # Ptr |-> keys **
   (&( out # "<anonymous struct>" ->ₛ "values") # Ptr |-> values **
    (&( out # "<anonymous struct>" ->ₛ "size") # Int |-> size **
     (store_string test_pre input **
      (CharArray.seg keys 0 size key_list **
       (CharArray.undef_seg keys size 256 **
        (IntArray.seg values 0 size value_list **
         IntArray.undef_seg values size 256)))))))
  |-- “ out <> 0 ” && “ keys <> 0 ” && “ values <> 0 ” &&
      “ 0 <= size ” && “ size <= 256 ” &&
      “ Zlength key_list = size ” && “ Zlength value_list = size ” &&
      “ P ” &&
      store_string test_pre input **
      &( out # "<anonymous struct>" ->ₛ "keys") # Ptr |-> keys **
      &( out # "<anonymous struct>" ->ₛ "values") # Ptr |-> values **
      &( out # "<anonymous struct>" ->ₛ "size") # Int |-> size **
      CharArray.seg keys 0 size key_list **
      CharArray.undef_seg keys size 256 **
      IntArray.seg values 0 size value_list **
      IntArray.undef_seg values size 256.
Proof.
  intros P test_pre input out keys values size key_list value_list
    Hout Hkeys Hvalues Hsize0 Hsize256 Hkeylen Hvallen HP.
  andp_assoc_change.
  apply coq_prop_andp_right; [|exact Hout].
  apply coq_prop_andp_right; [|exact Hkeys].
  apply coq_prop_andp_right; [|exact Hvalues].
  apply coq_prop_andp_right; [|exact Hsize0].
  apply coq_prop_andp_right; [|exact Hsize256].
  apply coq_prop_andp_right; [|exact Hkeylen].
  apply coq_prop_andp_right; [|exact Hvallen].
  apply coq_prop_andp_right; [|exact HP].
  sepcon_assoc_change.
  sepcon_lift (store_string test_pre input).
  derivable1_refl_tac.
Qed.

Local Transparent selected_keys_111 counts_at_111 max_count_z_111.

Lemma firstn_succ_nth_111 : forall (n : nat) (xs : list Z),
  (n < length xs)%nat ->
  firstn (S n) xs = firstn n xs ++ [nth n xs 0].
Proof.
  induction n as [|n IH]; intros xs Hlt.
  - destruct xs; [simpl in Hlt; lia | reflexivity].
  - destruct xs as [|x xs]; [simpl in Hlt; lia |].
    simpl. f_equal. apply IH. simpl in Hlt. lia.
Qed.

Lemma firstn_step_111 : forall (xs : list Z) i,
  0 <= i < Zlength xs ->
  firstn (Z.to_nat (i + 1)) xs =
  firstn (Z.to_nat i) xs ++ [Znth i xs 0].
Proof.
  intros xs i Hi.
  assert (Hnat : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hnat. apply firstn_succ_nth_111.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. lia.
Qed.

Lemma prefix_letters_step_111 : forall input i,
  0 <= i < Zlength input -> Znth i input 0 <> 32 ->
  prefix_letters_111 input (i + 1) =
  prefix_letters_111 input i ++ [Znth i input 0].
Proof.
  intros input i Hi Hspace.
  unfold prefix_letters_111. rewrite firstn_step_111 by exact Hi.
  rewrite filter_app. simpl. unfold non_space_111.
  destruct (Z.eqb (Znth i input 0) 32) eqn:E; simpl.
  - apply Z.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma prefix_letters_space_step_111 : forall input i,
  0 <= i < Zlength input -> Znth i input 0 = 32 ->
  prefix_letters_111 input (i + 1) = prefix_letters_111 input i.
Proof.
  intros input i Hi Hspace.
  unfold prefix_letters_111. rewrite firstn_step_111 by exact Hi.
  rewrite filter_app. unfold non_space_111. rewrite Hspace. simpl.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma count_byte_step_111 : forall letters x z,
  count_byte_111 (letters ++ [x]) z =
  if Z.eq_dec z x then count_byte_111 letters z + 1
  else count_byte_111 letters z.
Proof.
  intros letters x z. unfold count_byte_111.
  rewrite count_occ_app. simpl.
  destruct (Z.eq_dec z x) as [->|Hneq].
  - destruct (Z.eq_dec x x); [lia|contradiction].
  - destruct (Z.eq_dec x z); [congruence|lia].
Qed.

Lemma counts_at_step_111 : forall input i x,
  0 <= i < Zlength input -> x = Znth i input 0 -> x <> 32 ->
  0 <= x < 256 ->
  counts_at_111 input (i + 1) =
  replace_Znth x (Znth x (counts_at_111 input i) 0 + 1)
    (counts_at_111 input i).
Proof.
  intros input i x Hi Hx Hspace Hrange. subst x.
  apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - apply Nat2Z.inj. repeat rewrite <- Zlength_correct.
    rewrite Zlength_replace_Znth. reflexivity.
  - intros n Hn.
    rewrite counts_at_length_111 in Hn.
    rewrite nth_counts_at_111 by exact Hn.
    replace
      (nth n
        (replace_Znth (Znth i input 0)
          (Znth (Znth i input 0) (counts_at_111 input i) 0 + 1)
          (counts_at_111 input i)) 0)
      with
      (Znth (Z.of_nat n)
        (replace_Znth (Znth i input 0)
          (Znth (Znth i input 0) (counts_at_111 input i) 0 + 1)
          (counts_at_111 input i)) 0).
    2: { unfold Znth. rewrite Nat2Z.id. reflexivity. }
    rewrite prefix_letters_step_111 by assumption.
    rewrite count_byte_step_111.
    destruct (Z.eq_dec (Z.of_nat n) (Znth i input 0)) as [Heq|Hneq].
    + rewrite <- Heq. rewrite Znth_replace_Znth_Same.
      * unfold Znth. rewrite Nat2Z.id.
        rewrite nth_counts_at_111 by exact Hn. reflexivity.
      * rewrite Zlength_correct, counts_at_length_111. lia.
    + rewrite Znth_replace_Znth_Diff.
      * unfold Znth. rewrite Nat2Z.id.
        rewrite nth_counts_at_111 by exact Hn. reflexivity.
      * rewrite Zlength_correct, counts_at_length_111. lia.
      * rewrite Zlength_correct, counts_at_length_111. lia.
      * congruence.
Qed.

Lemma fold_max_replace_nth_111 : forall l n v,
  (n < length l)%nat -> nth n l 0 <= v ->
  fold_right Z.max 0 (replace_nth n l v) =
  Z.max v (fold_right Z.max 0 l).
Proof.
  induction l as [|a l IH]; intros n v Hn Hv; [simpl in Hn; lia|].
  destruct n as [|n].
  - simpl in *. rewrite Z.max_assoc.
    rewrite (Z.max_l v a) by lia. reflexivity.
  - simpl in *.
    rewrite (IH n v); [|lia|exact Hv].
    rewrite !Z.max_assoc. rewrite (Z.max_comm a v). reflexivity.
Qed.

Lemma max_count_replace_inc_111 : forall counts x,
  0 <= x < Zlength counts ->
  max_count_z_111
    (replace_Znth x (Znth x counts 0 + 1) counts) =
  Z.max (Znth x counts 0 + 1) (max_count_z_111 counts).
Proof.
  intros counts x Hx.
  unfold max_count_z_111, replace_Znth.
  apply fold_max_replace_nth_111.
  - rewrite Zlength_correct in Hx. lia.
  - unfold Znth. lia.
Qed.

Lemma byte_prefix_step_111 : forall ch,
  0 <= ch ->
  map Z.of_nat (seq 0 (Z.to_nat (ch + 1))) =
  map Z.of_nat (seq 0 (Z.to_nat ch)) ++ [ch].
Proof.
  intros ch Hch.
  replace (Z.to_nat (ch + 1)) with (S (Z.to_nat ch)).
  2: { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite seq_S, map_app. simpl. rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma selected_keys_step_yes_111 : forall counts max ch,
  0 <= ch -> Znth ch counts 0 = max -> 0 < max ->
  selected_keys_111 counts max (ch + 1) =
  selected_keys_111 counts max ch ++ [ch].
Proof.
  intros counts max ch Hch Heq Hmax.
  unfold selected_keys_111. rewrite byte_prefix_step_111 by exact Hch.
  rewrite filter_app. simpl. rewrite Heq, Z.eqb_refl.
  assert (Hltb : (0 <? max)%Z = true) by (apply Z.ltb_lt; exact Hmax).
  rewrite Hltb. reflexivity.
Qed.

Lemma selected_keys_step_count_no_111 : forall counts max ch,
  0 <= ch -> Znth ch counts 0 <> max ->
  selected_keys_111 counts max (ch + 1) =
  selected_keys_111 counts max ch.
Proof.
  intros counts max ch Hch Hneq.
  unfold selected_keys_111. rewrite byte_prefix_step_111 by exact Hch.
  rewrite filter_app. simpl.
  assert (Heqb : (Znth ch counts 0 =? max)%Z = false)
    by (apply Z.eqb_neq; exact Hneq).
  rewrite Heqb. simpl.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma selected_keys_step_max_no_111 : forall counts max ch,
  0 <= ch -> max <= 0 ->
  selected_keys_111 counts max (ch + 1) =
  selected_keys_111 counts max ch.
Proof.
  intros counts max ch Hch Hmax.
  unfold selected_keys_111. rewrite byte_prefix_step_111 by exact Hch.
  rewrite filter_app. simpl.
  assert (Hltb : (0 <? max)%Z = false) by (apply Z.ltb_ge; exact Hmax).
  rewrite Hltb.
  destruct (Znth ch counts 0 =? max)%Z; simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma output_prefix_step_yes_111 : forall counts max ch keys values,
  0 <= ch -> Znth ch counts 0 = max -> 0 < max ->
  problem_111_output_prefix_z counts max ch keys values ->
  problem_111_output_prefix_z counts max (ch + 1)
    (keys ++ [ch]) (values ++ [Znth ch counts 0]).
Proof.
  intros counts max ch keys values Hch Heq Hmax [Hkeys Hvalues].
  unfold problem_111_output_prefix_z. split.
  - rewrite selected_keys_step_yes_111 by assumption. now rewrite Hkeys.
  - unfold selected_values_111 in *. rewrite selected_keys_step_yes_111 by assumption.
    rewrite map_app. simpl. now rewrite Hvalues.
Qed.

Lemma output_prefix_step_count_no_111 : forall counts max ch keys values,
  0 <= ch -> Znth ch counts 0 <> max ->
  problem_111_output_prefix_z counts max ch keys values ->
  problem_111_output_prefix_z counts max (ch + 1) keys values.
Proof.
  intros counts max ch keys values Hch Hneq [Hkeys Hvalues].
  unfold problem_111_output_prefix_z. split.
  - rewrite selected_keys_step_count_no_111 by assumption. exact Hkeys.
  - unfold selected_values_111 in *. rewrite selected_keys_step_count_no_111 by assumption.
    exact Hvalues.
Qed.

Lemma output_prefix_step_max_no_111 : forall counts max ch keys values,
  0 <= ch -> max <= 0 ->
  problem_111_output_prefix_z counts max ch keys values ->
  problem_111_output_prefix_z counts max (ch + 1) keys values.
Proof.
  intros counts max ch keys values Hch Hmax [Hkeys Hvalues].
  unfold problem_111_output_prefix_z. split.
  - rewrite selected_keys_step_max_no_111 by assumption. exact Hkeys.
  - unfold selected_values_111 in *. rewrite selected_keys_step_max_no_111 by assumption.
    exact Hvalues.
Qed.

Lemma proof_of_histogram_safety_wit_15 : histogram_safety_wit_15.
Proof.
  unfold histogram_safety_wit_15. left. intros. Intros.
  pose proof (PreH12 (Znth i (c_string input) 0) ltac:(lia)) as Hcount.
  pose proof (c_string_nonzero_index_lt input i PreH6 PreH7 PreH5) as Hi.
  entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_1 : histogram_entail_wit_1.
Proof.
  unfold histogram_entail_wit_1. left. intros. Intros.
  unfold zeros. simpl. entailer!.
  rewrite IntArray.seg_empty.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&( "count")) 256).
  unfold store_string. cancel. entailer!.
  apply string_length_nonneg.
Qed.

Lemma proof_of_histogram_entail_wit_2 : histogram_entail_wit_2.
Proof.
  unfold histogram_entail_wit_2. left. intros. Intros.
  assert (Hz : zeros (i + 1) = zeros i ++ (0 :: nil)).
  {
    unfold zeros.
    replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite repeat_app. simpl. reflexivity.
  }
  unfold store_string. rewrite Hz. entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_3 : histogram_entail_wit_3.
Proof.
  unfold histogram_entail_wit_3. left. intros. Intros.
  assert (Hi : i = 256) by lia. subst i.
  subst size. subst max.
  assert (Hcounts : counts_at_111 input 0 = zeros 256).
  {
    unfold counts_at_111, prefix_letters_111, count_byte_111,
      byte_domain_111, zeros. simpl. reflexivity.
  }
  assert (Hlen : Zlength (zeros 256) = 256).
  {
    unfold zeros. rewrite Zlength_correct, repeat_length. reflexivity.
  }
  assert (Hzero : forall z : Z, 0 <= z < 256 -> Znth z (zeros 256) 0 = 0).
  {
    intros z Hz. unfold zeros. apply Znth_repeat_lt; lia.
  }
  Exists (zeros 256).
  rewrite IntArray.undef_seg_empty.
  sep_apply_l_atomic (IntArray.seg_to_full (&( "count")) 0 256 (zeros 256)).
  unfold problem_111_scan_state_z, max_count_z_111.
  rewrite Hcounts. simpl.
  replace (&( "count") + 0 * sizeof (INT)) with (&( "count")) by lia.
  replace (&( "count") + 0) with (&( "count")) by lia.
  replace (256 - 0) with 256 by lia.
  entailer!;
    intros z Hz; rewrite Hzero by exact Hz; lia.
Qed.

Lemma proof_of_histogram_entail_wit_4_1 : histogram_entail_wit_4_1.
Proof.
  unfold histogram_entail_wit_4_1. left. intros. Intros.
  assert (Hi : 0 <= i < string_length input).
  { split; [exact PreH7|].
    eapply c_string_nonzero_index_lt; eauto. }
  assert (Hx : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  rewrite Hx in *.
  set (x := Znth i input 0).
  set (counts' := replace_Znth x (Znth x counts_2 0 + 1) counts_2).
  assert (Hlen' : Zlength counts' = 256).
  { unfold counts'. rewrite Zlength_replace_Znth. exact PreH9. }
  assert (Hnew : Znth x counts' 0 = Znth x counts_2 0 + 1).
  { unfold counts'. apply Znth_replace_Znth_Same. lia. }
  destruct PreH16 as [Hcounts [Hmax Hbounds]].
  assert (Hstep : counts_at_111 input (i + 1) = counts').
  {
    unfold counts'. rewrite Hcounts.
    apply counts_at_step_111; unfold x; auto; lia.
  }
  assert (Hbounds' : forall z : Z,
    0 <= z < 256 -> 0 <= Znth z counts' 0 <= i + 1).
  {
    intros z Hz. destruct (Z.eq_dec z x) as [->|Hneq].
    - rewrite Hnew. specialize (Hbounds x ltac:(lia)). lia.
    - unfold counts'. rewrite Znth_replace_Znth_Diff; try lia.
      pose proof (Hbounds z Hz). lia.
  }
  assert (Hmax' : max_count_z_111 counts' = Znth x counts' 0).
  {
    unfold counts'. rewrite max_count_replace_inc_111 by lia.
    rewrite Znth_replace_Znth_Same by lia.
    rewrite <- Hmax. apply Z.max_l.
    assert (Hgt : Znth x counts_2 0 + 1 > max).
    {
      unfold x. rewrite Znth_replace_Znth_Same in PreH1; [exact PreH1|lia].
    }
    lia.
  }
  Exists counts'.
  unfold problem_111_scan_state_z.
  entailer!.
  - pose proof (Hbounds' x ltac:(lia)). lia.
Qed.

Lemma proof_of_histogram_entail_wit_4_2 : histogram_entail_wit_4_2.
Proof.
  unfold histogram_entail_wit_4_2. left. intros. Intros.
  assert (Hi : 0 <= i < string_length input).
  { split; [exact PreH7|].
    eapply c_string_nonzero_index_lt; eauto. }
  assert (Hx : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  rewrite Hx in *.
  set (x := Znth i input 0).
  set (counts' := replace_Znth x (Znth x counts_2 0 + 1) counts_2).
  assert (Hlen' : Zlength counts' = 256).
  { unfold counts'. rewrite Zlength_replace_Znth. exact PreH9. }
  assert (Hnew : Znth x counts' 0 = Znth x counts_2 0 + 1).
  { unfold counts'. apply Znth_replace_Znth_Same. lia. }
  destruct PreH16 as [Hcounts [Hmax Hbounds]].
  assert (Hstep : counts_at_111 input (i + 1) = counts').
  {
    unfold counts'. rewrite Hcounts.
    apply counts_at_step_111; unfold x; auto; lia.
  }
  assert (Hbounds' : forall z : Z,
    0 <= z < 256 -> 0 <= Znth z counts' 0 <= i + 1).
  {
    intros z Hz. destruct (Z.eq_dec z x) as [->|Hneq].
    - rewrite Hnew. specialize (Hbounds x ltac:(lia)). lia.
    - unfold counts'. rewrite Znth_replace_Znth_Diff; try lia.
      pose proof (Hbounds z Hz). lia.
  }
  assert (Hle : Znth x counts_2 0 + 1 <= max).
  {
    unfold x. rewrite Znth_replace_Znth_Same in PreH1; [exact PreH1|lia].
  }
  assert (Hmax' : max_count_z_111 counts' = max).
  {
    unfold counts'. rewrite max_count_replace_inc_111 by lia.
    rewrite <- Hmax. apply Z.max_r. exact Hle.
  }
  Exists counts'.
  unfold problem_111_scan_state_z.
  entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_4_3 : histogram_entail_wit_4_3.
Proof.
  unfold histogram_entail_wit_4_3. left. intros. Intros.
  assert (Hi : 0 <= i < string_length input).
  { split; [exact PreH4|].
    eapply c_string_nonzero_index_lt; eauto. }
  pose proof (c_string_Znth_inside input i 0 Hi) as Hx.
  pose proof (PreH12 i Hi) as Hrange.
  rewrite Hx in PreH1. entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_4_4 : histogram_entail_wit_4_4.
Proof.
  unfold histogram_entail_wit_4_4. left. intros. Intros.
  assert (Hi : 0 <= i < string_length input).
  { split; [exact PreH5|].
    eapply c_string_nonzero_index_lt; eauto. }
  pose proof (c_string_Znth_inside input i 0 Hi) as Hx.
  pose proof (PreH13 i Hi) as Hrange.
  rewrite Hx in PreH1. entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_4_5 : histogram_entail_wit_4_5.
Proof.
  unfold histogram_entail_wit_4_5. left. intros. Intros.
  assert (Hi : 0 <= i < string_length input).
  { split; [exact PreH3|].
    eapply c_string_nonzero_index_lt; eauto. }
  assert (Hx : Znth i (c_string input) 0 = Znth i input 0).
  { apply c_string_Znth_inside. exact Hi. }
  rewrite Hx in PreH1.
  destruct PreH12 as [Hcounts [Hmax Hbounds]].
  assert (Hstep : counts_at_111 input (i + 1) = counts_at_111 input i).
  {
    unfold counts_at_111. rewrite prefix_letters_space_step_111; auto.
  }
  Exists counts_2.
  unfold problem_111_scan_state_z.
  entailer!.
  - rewrite Hstep. exact Hcounts.
  - intros z Hz. pose proof (Hbounds z Hz). lia.
  - intros z Hz. pose proof (Hbounds z Hz). lia.
Qed.

Lemma proof_of_histogram_entail_wit_5 : histogram_entail_wit_5.
Proof.
  unfold histogram_entail_wit_5. left. intros. Intros.
  assert (Hi : i = string_length input).
  { eapply c_string_zero_index_eq_length; eauto. }
  subst i. subst size.
  Exists (@nil Z) (@nil Z) counts_2.
  unfold problem_111_output_prefix_z, selected_keys_111,
    selected_values_111, byte_domain_111. simpl.
  rewrite CharArray.seg_empty, IntArray.seg_empty.
  sep_apply_l_atomic (CharArray.undef_full_to_undef_seg keys 256).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg values 256).
  entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_6_1 : histogram_entail_wit_6_1.
Proof.
  unfold histogram_entail_wit_6_1. left. intros. Intros.
  assert (Hprefix : problem_111_output_prefix_z counts_2 max (ch + 1)
    (key_list_2 ++ [ch]) (value_list_2 ++ [Znth ch counts_2 0])).
  {
    eapply output_prefix_step_yes_111.
    - exact PreH6.
    - exact PreH2.
    - lia.
    - exact PreH15.
  }
  Exists (value_list_2 ++ [Znth ch counts_2 0])
    (key_list_2 ++ [ch]) counts_2.
  unfold store_string. entailer!.
  - rewrite Zlength_app.
    change (Zlength value_list_2 + 1 = size + 1). lia.
  - rewrite Zlength_app.
    change (Zlength key_list_2 + 1 = size + 1). lia.
Qed.

Lemma proof_of_histogram_entail_wit_6_2 : histogram_entail_wit_6_2.
Proof.
  unfold histogram_entail_wit_6_2. left. intros. Intros.
  assert (Hprefix : problem_111_output_prefix_z counts_2 max (ch + 1)
    key_list_2 value_list_2).
  { eapply output_prefix_step_count_no_111; eauto. }
  Exists value_list_2 key_list_2 counts_2.
  unfold store_string. entailer!.
Qed.

Lemma proof_of_histogram_entail_wit_6_3 : histogram_entail_wit_6_3.
Proof.
  unfold histogram_entail_wit_6_3. left. intros. Intros.
  assert (Hprefix : problem_111_output_prefix_z counts_2 max (ch + 1)
    key_list_2 value_list_2).
  { eapply output_prefix_step_max_no_111; eauto. }
  Exists value_list_2 key_list_2 counts_2.
  unfold store_string. entailer!.
Qed.

Lemma proof_of_histogram_return_wit_1 : histogram_return_wit_1.
Proof.
  unfold histogram_return_wit_1. intros. Intros.
  assert (Hch : ch = 256) by lia. subst ch.
  assert (Hinput_range : Forall byte_range_111 input).
  { apply Forall_byte_range_of_Znth_111. intros k Hk.
    apply PreH13. unfold string_length. exact Hk. }
  unfold problem_111_scan_state_z in PreH11.
  destruct PreH11 as [Hcounts [Hmax _]].
  assert (Hspec : problem_111_spec_z input key_list_2 value_list_2).
  { eapply operational_spec_111.
    - exact Hinput_range.
    - exact Hcounts.
    - exact Hmax.
    - exact PreH12. }
  clear Hinput_range Hcounts Hmax PreH10 PreH12 PreH13.
  Right.
  Exists value_list_2 key_list_2 size_2 values_2 keys_2.
  eapply package_histogram_result_111; eauto; lia.
Qed.
