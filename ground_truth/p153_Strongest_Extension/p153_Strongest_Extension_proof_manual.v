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

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope bool_scope.
Import ListNotations.
Import naive_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac.



Lemma row_payload_c_string_153 : forall s,
  row_payload_z_153 (string_lib.c_string s) = s.
Proof.
  intros s.
  unfold row_payload_z_153, string_lib.c_string.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  change (Z.succ 0) with 1.
  replace (Zlength s + 1 - 1) with (Zlength s) by lia.
  rewrite Zlength_correct, Nat2Z.id.
  rewrite firstn_app.
  rewrite firstn_all.
  rewrite Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma c_string_payload_prefix_153 : forall s,
  sublist 0 (string_length s) (c_string s) = s.
Proof.
  intros s.
  unfold c_string, string_length.
  apply sublist_app_exact1.
Qed.

Lemma c_string_null_suffix_153 : forall s,
  sublist (string_length s) (string_length s + 1) (c_string s) = cons 0 nil.
Proof.
  intros s.
  unfold c_string, string_length.
  unfold sublist.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  replace (Z.to_nat (Z.of_nat (List.length s))) with (List.length s) by lia.
  replace (Z.to_nat (Z.of_nat (List.length s) + 1)) with (S (List.length s)) by lia.
  rewrite firstn_all2 by (rewrite app_length; simpl; lia).
  rewrite skipn_app.
  rewrite skipn_all2 by lia.
  replace (List.length s - List.length s)%nat with 0%nat by lia.
  reflexivity.
Qed.

Lemma rows_well_formed_153_row : forall rows n k,
  rows_well_formed_153 rows n ->
  0 <= k < n ->
  let row := Znth k rows nil in
  let payload := row_payload_z_153 row in
  row = string_lib.c_string payload /\
  string_lib.valid_string payload /\
  string_lib.string_length payload <= 100 /\
  string_lib.string_length payload < INT_MAX /\
  Zlength row = string_lib.string_length payload + 1.
Proof.
  intros rows n k [Hlen Hwf] Hk row payload.
  specialize (Hwf k Hk).
  destruct Hwf as [Hrow [Hall [Hnul [Hle Hlt]]]].
  split; [exact Hrow|].
  split; [unfold string_lib.valid_string; exact (conj Hall Hnul)|].
  split; [exact Hle|].
  split; [exact Hlt|].
  subst row payload.
  rewrite Hrow at 1.
  unfold string_lib.c_string, string_lib.string_length.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma rows_well_formed_153_char_bound : forall rows n i j,
  rows_well_formed_153 rows n ->
  0 <= i < n ->
  0 <= j < string_lib.string_length (row_payload_z_153 (Znth i rows nil)) ->
  0 <= Znth j (Znth i rows nil) 0 <= 127.
Proof.
  intros rows n i j Hwf Hi Hj.
  pose proof (rows_well_formed_153_row rows n i Hwf Hi) as Hrow.
  destruct Hrow as [Hrow_eq Hrow_tail].
  destruct Hrow_tail as [Hvalid Hrow_tail].
  destruct Hrow_tail as [Hle Hrow_tail].
  destruct Hrow_tail as [Hlt Hrow_len].
  rewrite Hrow_eq.
  rewrite string_lib.c_string_Znth_inside by exact Hj.
  unfold string_lib.valid_string in Hvalid.
  destruct Hvalid as (Hall & Hnul).
  apply Hall.
  unfold string_lib.string_length in Hj.
  lia.
Qed.

Lemma strength_scan_state_153_initial : forall s,
  strength_scan_state_153 s 0 0.
Proof.
  intros s.
  unfold strength_scan_state_153.
  split.
  - unfold string_lib.string_length. rewrite Zlength_correct. lia.
  - split.
    + unfold sublist. reflexivity.
    + lia.
Qed.

Lemma extension_strength_z_app_single : forall s c,
  extension_strength_z (s ++ [c]) =
  extension_strength_z s + char_strength_delta_153 c.
Proof.
  induction s as [|x xs IH]; intros c; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma char_strength_delta_153_bound : forall c,
  -1 <= char_strength_delta_153 c <= 1.
Proof.
  intros c.
  unfold char_strength_delta_153.
  destruct (is_upper_z_153 c); destruct (is_lower_z_153 c); lia.
Qed.

Lemma char_strength_delta_153_low : forall c,
  c < 65 ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [apply Z.leb_le in H65; lia|].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_mid : forall c,
  90 < c < 97 ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_upper : forall c,
  65 <= c <= 90 ->
  char_strength_delta_153 c = 1.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [|apply Z.leb_gt in H90; lia].
  destruct (Z.leb 97 c) eqn:H97; [apply Z.leb_le in H97; lia|].
  reflexivity.
Qed.

Lemma char_strength_delta_153_lower : forall c,
  97 <= c <= 122 ->
  char_strength_delta_153 c = -1.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [|apply Z.leb_gt in H97; lia].
  destruct (Z.leb c 122) eqn:H122; [|apply Z.leb_gt in H122; lia].
  reflexivity.
Qed.

Lemma char_strength_delta_153_high : forall c,
  122 < c ->
  char_strength_delta_153 c = 0.
Proof.
  intros c Hc.
  unfold char_strength_delta_153, is_upper_z_153, is_lower_z_153.
  destruct (Z.leb 65 c) eqn:H65; [|apply Z.leb_gt in H65; lia].
  destruct (Z.leb c 90) eqn:H90; [apply Z.leb_le in H90; lia|].
  destruct (Z.leb 97 c) eqn:H97; [|apply Z.leb_gt in H97; lia].
  destruct (Z.leb c 122) eqn:H122; [apply Z.leb_le in H122; lia|].
  reflexivity.
Qed.

Lemma strength_scan_state_153_step : forall s j strength c,
  0 <= j < string_lib.string_length s ->
  c = Znth j s 0 ->
  strength_scan_state_153 s j strength ->
  strength_scan_state_153 s (j + 1) (strength + char_strength_delta_153 c).
Proof.
  intros s j strength c Hj Hc [Hbounds [Hstrength Hrange]].
  unfold strength_scan_state_153.
  split; [lia|].
  split.
  - rewrite Hstrength.
    unfold string_lib.string_length in Hj.
    rewrite (sublist_split 0 (j + 1) j s) by lia.
    replace (sublist j (j + 1) s) with [Znth j s 0]
      by (symmetry; apply sublist_single; lia).
    rewrite extension_strength_z_app_single.
    subst c.
    lia.
  - pose proof (char_strength_delta_153_bound c).
    lia.
Qed.

Lemma strength_scan_state_153_step_eq : forall s j strength c new_strength,
  0 <= j < string_lib.string_length s ->
  c = Znth j s 0 ->
  strength_scan_state_153 s j strength ->
  new_strength = strength + char_strength_delta_153 c ->
  strength_scan_state_153 s (j + 1) new_strength.
Proof.
  intros s j strength c new_strength Hj Hc Hstate Hnew.
  subst new_strength.
  eapply strength_scan_state_153_step; eauto.
Qed.

Lemma strength_scan_state_153_finish : forall s j strength,
  j >= string_lib.string_length s ->
  strength_scan_state_153 s j strength ->
  strength = extension_strength_z s.
Proof.
  intros s j strength Hj [Hbounds [Hstrength _]].
  rewrite Hstrength.
  replace j with (string_lib.string_length s) by lia.
  unfold string_lib.string_length.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma best_prefix_state_153_initial : forall rows n,
  rows_well_formed_153 rows n ->
  0 < n ->
  best_prefix_state_153 rows 1 0
    (extension_strength_z (row_payload_z_153 (Znth 0 rows nil))).
Proof.
  intros rows n [Hlen Hwf] Hn.
  unfold best_prefix_state_153.
  rewrite Hlen.
  split; [lia|].
  split; [lia|].
  split; [reflexivity|].
  split.
  - intros j Hj.
    assert (j = 0) by lia.
    subst j.
    lia.
  - intros j Hj _.
    lia.
Qed.

Lemma best_prefix_state_153_step_keep : forall rows k best_idx max_strength cur_strength,
  best_prefix_state_153 rows k best_idx max_strength ->
  k < Zlength rows ->
  cur_strength = extension_strength_z (row_payload_z_153 (Znth k rows nil)) ->
  cur_strength <= max_strength ->
  best_prefix_state_153 rows (k + 1) best_idx max_strength.
Proof.
  intros rows k best_idx max_strength cur_strength Hstate Hk Hcur Hle.
  destruct Hstate as [Hbounds [Hbest [Hmax [Hall Hearliest]]]].
  unfold best_prefix_state_153.
  repeat split; try lia; auto.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + lia.
    + apply Hall. lia.
  - intros j Hj Heq.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + subst cur_strength.
      rewrite Heq in Hle.
      lia.
    + apply Hearliest; lia.
Qed.

Lemma best_prefix_state_153_step_update : forall rows k best_idx max_strength cur_strength,
  best_prefix_state_153 rows k best_idx max_strength ->
  k < Zlength rows ->
  cur_strength = extension_strength_z (row_payload_z_153 (Znth k rows nil)) ->
  max_strength < cur_strength ->
  best_prefix_state_153 rows (k + 1) k cur_strength.
Proof.
  intros rows k best_idx max_strength cur_strength Hstate Hk Hcur Hgt.
  destruct Hstate as [Hbounds [Hbest [Hmax [Hall Hearliest]]]].
  unfold best_prefix_state_153.
  repeat split; try lia; auto.
  - intros j Hj.
    destruct (Z.eq_dec j k) as [->|Hneq].
    + lia.
    + specialize (Hall j ltac:(lia)). lia.
  - intros j Hj Heq.
    destruct (Z.eq_dec j k) as [->|Hneq]; [lia|].
    specialize (Hall j ltac:(lia)).
    lia.
Qed.

Lemma string_of_list_z_153_app : forall a b,
  string_of_list_z_153 (a ++ b) =
  String.append (string_of_list_z_153 a) (string_of_list_z_153 b).
Proof.
  induction a as [|x xs IH]; intros b; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Lemma ascii_of_z_153_46 :
  ascii_of_z_153 46 = "."%char.
Proof.
  reflexivity.
Qed.

Lemma list_ascii_of_string_string_of_list_z_153 : forall l,
  list_ascii_of_string (string_of_list_z_153 l) = map ascii_of_z_153 l.
Proof.
  induction l; simpl; congruence.
Qed.

Lemma output_payload_string_153 : forall class_l ext_l,
  string_of_list_z_153 (output_payload_153 class_l ext_l) =
  (string_of_list_z_153 class_l ++ "." ++ string_of_list_z_153 ext_l)%string.
Proof.
  intros class_l ext_l.
  unfold output_payload_153.
  rewrite !string_of_list_z_153_app.
  simpl.
  rewrite ascii_of_z_153_46.
  reflexivity.
Qed.

Lemma N_of_ascii_of_z_153 : forall z,
  0 <= z < 256 ->
  N_of_ascii (ascii_of_z_153 z) = Z.to_N z.
Proof.
  intros z Hz.
  unfold ascii_of_z_153.
  apply Nnat.N2Nat.inj.
  change (nat_of_ascii (ascii_of_nat (Z.to_nat z)) = N.to_nat (Z.to_N z)).
  rewrite nat_ascii_embedding by lia.
  symmetry.
  apply Z_N_nat.
Qed.

Lemma ascii_leb_z_153 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  (ascii_of_z_153 a <=? ascii_of_z_153 b)%char = true <-> a <= b.
Proof.
  intros a b Ha Hb.
  split; intro H.
  - unfold Ascii.leb, Ascii.compare in H.
    rewrite !N_of_ascii_of_z_153 in H by lia.
    destruct (Z_le_gt_dec a b) as [|Hgt]; [lia|].
    assert ((Z.to_N a ?= Z.to_N b)%N = Gt)
      by (apply N.compare_gt_iff; lia).
    rewrite H0 in H.
    discriminate.
  - unfold Ascii.leb, Ascii.compare.
    rewrite !N_of_ascii_of_z_153 by lia.
    destruct (Z.to_N a ?= Z.to_N b)%N eqn:Hcmp; auto.
    apply N.compare_gt_iff in Hcmp.
    lia.
Qed.

Lemma is_uppercase_of_z_153 : forall c,
  0 <= c <= 127 ->
  is_uppercase (ascii_of_z_153 c) = is_upper_z_153 c.
Proof.
  intros c Hc.
  unfold is_uppercase, is_upper_z_153.
  change "A"%char with (ascii_of_z_153 65).
  change "Z"%char with (ascii_of_z_153 90).
  destruct (Z.leb_spec 65 c) as [H65|H65];
    destruct (Z.leb_spec c 90) as [H90|H90]; simpl.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = true)
      by (apply ascii_leb_z_153; lia).
    assert ((ascii_of_z_153 c <=? ascii_of_z_153 90)%char = true)
      by (apply ascii_leb_z_153; lia).
    rewrite H, H0. reflexivity.
  - assert ((ascii_of_z_153 c <=? ascii_of_z_153 90)%char = false).
    { destruct (ascii_of_z_153 c <=? ascii_of_z_153 90)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char; reflexivity.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
  - assert ((ascii_of_z_153 65 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 65 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
Qed.

Lemma is_lowercase_of_z_153 : forall c,
  0 <= c <= 127 ->
  is_lowercase (ascii_of_z_153 c) = is_lower_z_153 c.
Proof.
  intros c Hc.
  unfold is_lowercase, is_lower_z_153.
  change "a"%char with (ascii_of_z_153 97).
  change "z"%char with (ascii_of_z_153 122).
  destruct (Z.leb_spec 97 c) as [H97|H97];
    destruct (Z.leb_spec c 122) as [H122|H122]; simpl.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = true)
      by (apply ascii_leb_z_153; lia).
    assert ((ascii_of_z_153 c <=? ascii_of_z_153 122)%char = true)
      by (apply ascii_leb_z_153; lia).
    rewrite H, H0. reflexivity.
  - assert ((ascii_of_z_153 c <=? ascii_of_z_153 122)%char = false).
    { destruct (ascii_of_z_153 c <=? ascii_of_z_153 122)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char; reflexivity.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
  - assert ((ascii_of_z_153 97 <=? ascii_of_z_153 c)%char = false).
    { destruct (ascii_of_z_153 97 <=? ascii_of_z_153 c)%char eqn:Hcmp; auto.
      apply ascii_leb_z_153 in Hcmp; lia. }
    rewrite H. reflexivity.
Qed.

Lemma strength_string_cons_153 : forall c s,
  strength (String c s) = ascii_strength_delta_153 c + strength s.
Proof.
  intros c s.
  unfold strength, ascii_strength_delta_153, count_pred.
  cbn [list_ascii_of_string filter length].
  destruct (is_uppercase c); destruct (is_lowercase c);
    repeat match goal with
    | |- context[Datatypes.length (?x :: ?xs)] =>
        change (Datatypes.length (x :: xs)) with (S (Datatypes.length xs))
    end;
    rewrite ?Nat2Z.inj_succ; lia.
Qed.

Lemma char_strength_delta_153_spec : forall c,
  0 <= c <= 127 ->
  char_strength_delta_153 c = ascii_strength_delta_153 (ascii_of_z_153 c).
Proof.
  intros c Hc.
  unfold char_strength_delta_153, ascii_strength_delta_153.
  rewrite is_uppercase_of_z_153 by lia.
  rewrite is_lowercase_of_z_153 by lia.
  reflexivity.
Qed.

Lemma all_ascii_cons_153 : forall c rest,
  string_lib.all_ascii (c :: rest) ->
  0 <= c <= 127 /\ string_lib.all_ascii rest.
Proof.
  intros c rest Hall.
  split.
  - specialize (Hall 0).
    unfold string_lib.string_length in Hall.
    replace (Znth 0 (c :: rest) 0) with c in Hall by reflexivity.
    apply Hall.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
  - intros i Hi.
    specialize (Hall (i + 1)).
    unfold string_lib.string_length in *.
    rewrite Znth_cons in Hall by lia.
    replace (i + 1 - 1) with i in Hall by lia.
    apply Hall.
    rewrite Zlength_cons.
    pose proof (Zlength_nonneg rest).
    lia.
Qed.

Lemma extension_strength_z_spec_strength : forall s,
  string_lib.all_ascii s ->
  extension_strength_z s = strength (string_of_list_z_153 s).
Proof.
  induction s as [|c rest IH]; intros Hall.
  - reflexivity.
  - simpl.
    rewrite strength_string_cons_153.
    pose proof (all_ascii_cons_153 c rest Hall) as [Hc Hrest].
    rewrite IH by exact Hrest.
    rewrite char_strength_delta_153_spec by exact Hc.
    reflexivity.
Qed.

Lemma rows_well_formed_153_row_strength : forall rows n i,
  rows_well_formed_153 rows n ->
  0 <= i < n ->
  extension_strength_z (row_payload_z_153 (Znth i rows nil)) =
  strength (row_string_z_153 (Znth i rows nil)).
Proof.
  intros rows n i Hwf Hi.
  pose proof (rows_well_formed_153_row rows n i Hwf Hi) as Hrow.
  destruct Hrow as [_ [Hvalid _]].
  unfold row_string_z_153.
  apply extension_strength_z_spec_strength.
  destruct Hvalid as [Hall _].
  exact Hall.
Qed.

Lemma rows_to_strings_z_153_split_best : forall rows n best_idx,
  Zlength rows = n ->
  0 <= best_idx < n ->
  rows_to_strings_z_153 rows =
    map row_string_z_153 (firstn (Z.to_nat best_idx) rows) ++
    row_string_z_153 (Znth best_idx rows nil) ::
    map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows).
Proof.
  intros rows n best_idx Hlen Hbest.
  unfold rows_to_strings_z_153.
  change (row_string_z_153 (Znth best_idx rows nil) ::
          map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows))
    with (map row_string_z_153
            (Znth best_idx rows nil :: skipn (S (Z.to_nat best_idx)) rows)).
  rewrite <- map_app.
  apply f_equal.
  symmetry.
  apply firstn_skipn_middle.
  apply nth_error_nth'.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct.
  lia.
Qed.

Lemma best_prefix_state_153_problem_spec : forall class_l rows n best_idx max_strength,
  rows_well_formed_153 rows n ->
  problem_153_pre_z class_l rows ->
  best_prefix_state_153 rows n best_idx max_strength ->
  problem_153_spec_z
    class_l rows
    (output_payload_153 class_l (row_payload_z_153 (Znth best_idx rows nil))).
Proof.
  intros class_l rows n best_idx max_strength Hwf _ Hbest.
  destruct Hwf as [Hlen Hwf_rows].
  destruct Hbest as [Hk [Hbest_range [Hmax [Hall Hearliest]]]].
  assert (Hbest_n : 0 <= best_idx < n) by lia.
  assert (Hn_pos : 0 < n) by lia.
  pose proof (rows_to_strings_z_153_split_best rows n best_idx Hlen Hbest_n)
    as Hsplit.
  set (best_row := Znth best_idx rows nil).
  set (best_s := row_string_z_153 best_row).
  set (prefix := map row_string_z_153 (firstn (Z.to_nat best_idx) rows)).
  set (post := map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows)).
  assert (Hbest_strength :
    extension_strength_z (row_payload_z_153 best_row) = strength best_s).
  { subst best_row best_s.
    apply rows_well_formed_153_row_strength with (n := n); [split; auto|lia]. }
  change (Znth best_idx rows nil) with best_row in Hmax.
  assert (Hprefix_lt : forall e, In e prefix -> (strength e < strength best_s)%Z).
  {
    intros e Hin.
    subst prefix.
    apply in_map_iff in Hin.
    destruct Hin as [row [He Hrow_in]].
    apply In_nth with (d := @nil Z) in Hrow_in.
    destruct Hrow_in as [m [Hm Hnth]].
    rewrite firstn_length in Hm.
    rewrite Nat.min_glb_lt_iff in Hm.
    destruct Hm as [Hm_best Hm_rows].
    assert (Hm_best_nat : (m < Z.to_nat best_idx)%nat) by exact Hm_best.
    assert (Hj_range : 0 <= Z.of_nat m < n)
      by (rewrite Zlength_correct in Hlen; apply Nat2Z.inj_lt in Hm_rows; lia).
    assert (Hj_best : Z.of_nat m < best_idx)
      by (apply Nat2Z.inj_lt in Hm_best; rewrite Z2Nat.id in Hm_best by lia; lia).
    rewrite nth_firstn in Hnth by exact Hm_best_nat.
    assert (Hrow_eq : row = Znth (Z.of_nat m) rows nil)
      by (subst row; unfold Znth; rewrite Nat2Z.id; reflexivity).
    subst e.
    rewrite Hrow_eq.
    pose proof (Hall (Z.of_nat m) ltac:(lia)) as Hle.
    pose proof (Hearliest (Z.of_nat m) ltac:(lia)) as Hear.
    pose proof (rows_well_formed_153_row_strength rows n (Z.of_nat m)
      (conj Hlen Hwf_rows) Hj_range) as Hrow_strength.
    rewrite Hrow_strength in Hle.
    rewrite Hbest_strength in Hmax.
    rewrite Hmax in Hle.
    assert (Hstrict :
      strength (row_string_z_153 (Znth (Z.of_nat m) rows nil)) <
      strength best_s) by (
      assert (Hneq :
        strength (row_string_z_153 (Znth (Z.of_nat m) rows nil)) <>
        strength best_s) by
        (intro Heq_strength;
        assert (extension_strength_z (row_payload_z_153 (Znth (Z.of_nat m) rows nil)) =
                max_strength) as Heq_ext by (rewrite Hrow_strength; rewrite Hmax; lia);
        specialize (Hear Heq_ext);
        lia);
      lia).
    exact Hstrict.
  }
  assert (Hpost_le : forall e, In e post -> (strength e <= strength best_s)%Z).
  {
    intros e Hin.
    subst post.
    apply in_map_iff in Hin.
    destruct Hin as [row [He Hrow_in]].
    apply In_nth with (d := @nil Z) in Hrow_in.
    destruct Hrow_in as [m [Hm Hnth]].
    set (j := best_idx + 1 + Z.of_nat m).
    assert (Hj_range : 0 <= j < n).
    {
      subst j.
      rewrite skipn_length in Hm.
      rewrite Zlength_correct in Hlen.
      apply Nat2Z.inj_lt in Hm.
      rewrite Nat2Z.inj_sub in Hm by
        (apply Nat2Z.inj_le; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia).
      rewrite Nat2Z.inj_succ in Hm.
      rewrite Z2Nat.id in Hm by lia.
      lia.
    }
    assert (Hrow_eq : row = Znth j rows nil).
    {
      subst j.
      rewrite nth_skipn in Hnth.
      unfold Znth.
      rewrite <- Hnth.
      f_equal.
      rewrite Z2Nat.inj_add by lia.
      replace (Z.to_nat (best_idx + 1)) with (S (Z.to_nat best_idx)) by
        (apply Nat2Z.inj; rewrite Nat2Z.inj_succ; rewrite !Z2Nat.id by lia; lia).
      lia.
    }
    subst e.
    rewrite Hrow_eq.
    pose proof (Hall j ltac:(lia)) as Hle.
    pose proof (rows_well_formed_153_row_strength rows n j
      (conj Hlen Hwf_rows) Hj_range) as Hrow_strength.
    rewrite Hrow_strength in Hle.
    rewrite Hbest_strength in Hmax.
    rewrite Hmax in Hle.
    exact Hle.
  }
  unfold problem_153_spec_z, problem_153_spec.
  rewrite Hsplit.
  change (map row_string_z_153 (firstn (Z.to_nat best_idx) rows)) with prefix.
  change (map row_string_z_153 (skipn (S (Z.to_nat best_idx)) rows)) with post.
  destruct prefix as [|p prefix']; simpl.
  - exists best_s.
    split.
    + unfold is_strongest.
      exists [], post.
      split; [reflexivity|].
      split; [intro Hin; inversion Hin|].
      split.
      * intros e Hin. inversion Hin.
      * exact Hpost_le.
    + rewrite output_payload_string_153.
      subst best_s best_row.
      reflexivity.
  - exists best_s.
    split.
    + unfold is_strongest.
      exists (p :: prefix'), post.
      split; [reflexivity|].
      split.
      * intro Hin.
        pose proof (Hprefix_lt best_s Hin).
        lia.
      * split; [exact Hprefix_lt|exact Hpost_le].
    + rewrite output_payload_string_153.
      subst best_s best_row.
      reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

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
