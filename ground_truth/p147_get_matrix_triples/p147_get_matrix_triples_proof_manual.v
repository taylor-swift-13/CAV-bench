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
From SimpleC.EE.CAV.ground_truth_p147_get_matrix_triples Require Import p147_get_matrix_triples_goal.
From SimpleC.EE.CAV.ground_truth_p147_get_matrix_triples Require Import p147_get_matrix_triples_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p147_get_matrix_triples.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope Z_scope.
Import ListNotations.
Local Open Scope Z_scope.



Lemma triples_k_nonneg_147 : forall n i j fuel,
  0 <= triples_k_aux_147 n i j fuel.
Proof.
  induction fuel; simpl; intros; try lia.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); lia.
Qed.

Lemma triples_k_bound_147 : forall n i j fuel,
  triples_k_aux_147 n i j fuel <= Z.of_nat fuel.
Proof.
  induction fuel; simpl; intros; try lia.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); lia.
Qed.

Lemma triples_k_bound_z_147 : forall n i j k,
  triples_k_147 n i j k <= Z.of_nat (Z.to_nat (k - (j + 1))).
Proof.
  intros. unfold triples_k_147. apply triples_k_bound_147.
Qed.

Lemma triples_k_step_raw_147 : forall n i j k,
  j + 1 <= k ->
  triples_k_147 n i j (k + 1) =
  triples_k_147 n i j k +
  if triple_good_bool_147 i j k then 1 else 0.
Proof.
  intros n i j k Hjk.
  unfold triples_k_147.
  replace (Z.to_nat (k + 1 - (j + 1))) with
      (S (Z.to_nat (k - (j + 1)))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_k_aux_147].
  replace (j + 1 + Z.of_nat (Z.to_nat (k - (j + 1)))) with k by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_k_step_good_147 : forall n i j k,
  j + 1 <= k ->
  triple_good_bool_147 i j k = true ->
  triples_k_147 n i j (k + 1) = triples_k_147 n i j k + 1.
Proof.
  intros. rewrite triples_k_step_raw_147 by lia. rewrite H0. reflexivity.
Qed.

Lemma triples_k_step_bad_147 : forall n i j k,
  j + 1 <= k ->
  triple_good_bool_147 i j k = false ->
  triples_k_147 n i j (k + 1) = triples_k_147 n i j k.
Proof.
  intros. rewrite triples_k_step_raw_147 by lia. rewrite H0. lia.
Qed.

Lemma triples_j_step_147 : forall n i j,
  i + 1 <= j ->
  triples_j_147 n i (j + 1) =
  triples_j_147 n i j + triples_k_147 n i j (n + 1).
Proof.
  intros n i j Hij.
  unfold triples_j_147.
  replace (Z.to_nat (j + 1 - (i + 1))) with
      (S (Z.to_nat (j - (i + 1)))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_j_aux_147].
  replace (i + 1 + Z.of_nat (Z.to_nat (j - (i + 1)))) with j by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_i_step_147 : forall n i,
  1 <= i ->
  triples_i_147 n (i + 1) =
  triples_i_147 n i + triples_j_147 n i (n + 1).
Proof.
  intros n i Hi.
  unfold triples_i_147.
  replace (Z.to_nat (i + 1 - 1)) with (S (Z.to_nat (i - 1))).
  2:{
    rewrite <- Z2Nat.inj_succ by lia.
    f_equal; lia.
  }
  cbn [triples_i_aux_147].
  replace (1 + Z.of_nat (Z.to_nat (i - 1))) with i by
    (rewrite Z2Nat.id by lia; lia).
  reflexivity.
Qed.

Lemma triples_j_nonneg_147 : forall n i j,
  0 <= triples_j_147 n i j.
Proof.
  intros n i j.
  unfold triples_j_147.
  induction (Z.to_nat (j - (i + 1))); cbn [triples_j_aux_147]; try lia.
  unfold triples_k_147.
  pose proof (triples_k_nonneg_147 n i (i + 1 + Z.of_nat n0)
    (Z.to_nat (n + 1 - (i + 1 + Z.of_nat n0 + 1)))).
  lia.
Qed.

Lemma triples_j_aux_bound_147 : forall n i fuel,
  1 <= i + 1 ->
  i + 1 + Z.of_nat fuel <= n + 1 ->
  n <= 1004 ->
  triples_j_aux_147 n i fuel <= Z.of_nat fuel * 1004.
Proof.
  induction fuel; intros Hi Hfuel Hn; cbn [triples_j_aux_147]; try lia.
  pose proof (IHfuel Hi ltac:(lia) Hn).
  pose proof (triples_k_bound_z_147 n i (i + 1 + Z.of_nat fuel) (n + 1)).
  assert (Z.of_nat (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) <= 1004).
  {
    rewrite ZifyInst.of_nat_to_nat_eq. lia.
  }
  lia.
Qed.

Lemma triples_j_bound_147 : forall n i j,
  n <= 1004 ->
  1 <= i + 1 ->
  i + 1 <= n + 1 ->
  j <= n + 1 ->
  triples_j_147 n i j <= Z.of_nat (Z.to_nat (j - (i + 1))) * 1004.
Proof.
  intros n i j Hn Hi Hin Hj.
  unfold triples_j_147.
  apply triples_j_aux_bound_147.
  - assumption.
  - rewrite ZifyInst.of_nat_to_nat_eq. lia.
  - assumption.
Qed.

Lemma triples_i_nonneg_147 : forall n i,
  0 <= triples_i_147 n i.
Proof.
  intros n i.
  unfold triples_i_147.
  induction (Z.to_nat (i - 1)); cbn [triples_i_aux_147]; try lia.
  pose proof (triples_j_nonneg_147 n (1 + Z.of_nat n0) (n + 1)).
  lia.
Qed.

Lemma triples_i_aux_bound_147 : forall n fuel,
  1 + Z.of_nat fuel <= n + 1 ->
  n <= 1004 ->
  triples_i_aux_147 n fuel <= Z.of_nat fuel * 1004 * 1004.
Proof.
  induction fuel; intros Hfuel Hn; cbn [triples_i_aux_147]; try lia.
  pose proof (IHfuel ltac:(lia) Hn).
  pose proof (triples_j_bound_147 n (1 + Z.of_nat fuel) (n + 1) Hn ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (Z.of_nat (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) <= 1004).
  {
    rewrite ZifyInst.of_nat_to_nat_eq. lia.
  }
  lia.
Qed.

Lemma triples_i_bound_147 : forall n i,
  n <= 1004 ->
  1 <= i ->
  i <= n + 1 ->
  triples_i_147 n i <= Z.of_nat (Z.to_nat (i - 1)) * 1004 * 1004.
Proof.
  intros n i Hn Hlow Hi.
  unfold triples_i_147.
  apply triples_i_aux_bound_147.
  - rewrite ZifyInst.of_nat_to_nat_eq. lia.
  - assumption.
Qed.

Lemma triples_partial_bound_147 : forall n i j k,
  1 <= n <= 1004 ->
  1 <= i <= n ->
  i < j <= n ->
  j + 1 <= k <= n + 1 ->
  triples_i_147 n i + triples_j_147 n i j + triples_k_147 n i j k < INT_MAX.
Proof.
  intros n i j k Hn Hi Hj Hk.
  pose proof (triples_i_bound_147 n i ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (triples_j_bound_147 n i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (triples_k_bound_z_147 n i j k).
  assert (Z.of_nat (Z.to_nat (i - 1)) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  assert (Z.of_nat (Z.to_nat (j - (i + 1))) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  assert (Z.of_nat (Z.to_nat (k - (j + 1))) <= 1004).
  { rewrite Z2Nat.id by lia. lia. }
  lia.
Qed.

Lemma triples_k_nonneg_z_147 : forall n i j k,
  0 <= triples_k_147 n i j k.
Proof.
  intros. unfold triples_k_147. apply triples_k_nonneg_147.
Qed.

Lemma triple_value_range_147 : forall i,
  1 <= i <= 1004 ->
  0 <= triple_value_147 i <= 1007013.
Proof.
  unfold triple_value_147; intros; nia.
Qed.

Lemma triple_sum_range_147 : forall i j k,
  1 <= i <= 1004 ->
  1 <= j <= 1004 ->
  1 <= k <= 1004 ->
  0 <= triple_value_147 i + triple_value_147 j + triple_value_147 k <= 3021039.
Proof.
  intros.
  pose proof (triple_value_range_147 i H).
  pose proof (triple_value_range_147 j H0).
  pose proof (triple_value_range_147 k H1).
  lia.
Qed.

Lemma a_val_Z_to_nat_147 : forall z,
  0 <= z ->
  a_val (Z.to_nat z) = triple_value_147 z.
Proof.
  intros z Hz.
  unfold a_val, triple_value_147.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma triple_good_bool_valid_147 : forall n i j k,
  1 <= i < j ->
  j < k ->
  k <= n ->
  0 <= n ->
  triple_good_bool_147 i j k = true ->
  is_valid_triple (Z.to_nat n) (Z.to_nat i) (Z.to_nat j) (Z.to_nat k).
Proof.
  intros n i j k Hij Hjk Hkn Hn Hgood.
  unfold is_valid_triple.
  repeat split.
  - apply Nat2Z.inj_le. rewrite Z2Nat.id by lia. lia.
  - apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia.
  - apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia.
  - apply Nat2Z.inj_le; rewrite !Z2Nat.id by lia; lia.
  - unfold triple_good_bool_147 in Hgood.
    apply Z.eqb_eq in Hgood.
    rewrite !a_val_Z_to_nat_147 by lia.
    rewrite <- Z.rem_mod_nonneg.
    + exact Hgood.
    + unfold triple_value_147; nia.
    + lia.
Qed.

Lemma is_valid_triple_good_bool_147 : forall n i j k,
  is_valid_triple (Z.to_nat n) i j k ->
  0 <= n ->
  triple_good_bool_147 (Z.of_nat i) (Z.of_nat j) (Z.of_nat k) = true.
Proof.
  intros n i j k Hvalid Hn.
  destruct Hvalid as [Hi [Hij [Hjk [Hkn Hmod]]]].
  unfold triple_good_bool_147.
  apply Z.eqb_eq.
  rewrite Z.rem_mod_nonneg.
  - unfold triple_value_147.
    change (Z.of_nat i * Z.of_nat i - Z.of_nat i + 1) with (a_val i).
    change (Z.of_nat j * Z.of_nat j - Z.of_nat j + 1) with (a_val j).
    change (Z.of_nat k * Z.of_nat k - Z.of_nat k + 1) with (a_val k).
    exact Hmod.
  - unfold triple_value_147; nia.
  - lia.
Qed.

Lemma triples_k_list_length_147 : forall n i j fuel,
  Z.of_nat (length (triples_k_list_aux_147 n i j fuel)) =
  triples_k_aux_147 n i j fuel.
Proof.
  intros n i j fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_k_list_aux_147 triples_k_aux_147]. reflexivity.
  - cbn [triples_k_list_aux_147 triples_k_aux_147].
    destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)); try rewrite length_app; simpl; lia.
Qed.

Lemma triples_j_list_length_147 : forall n i fuel,
  Z.of_nat (length (triples_j_list_aux_147 n i fuel)) =
  triples_j_aux_147 n i fuel.
Proof.
  intros n i fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_j_list_aux_147 triples_j_aux_147]. reflexivity.
  - cbn [triples_j_list_aux_147 triples_j_aux_147].
    rewrite length_app, Nat2Z.inj_add, IHfuel, triples_k_list_length_147.
    reflexivity.
Qed.

Lemma triples_i_list_length_147 : forall n fuel,
  Z.of_nat (length (triples_i_list_aux_147 n fuel)) =
  triples_i_aux_147 n fuel.
Proof.
  intros n fuel.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_i_list_aux_147 triples_i_aux_147]. reflexivity.
  - cbn [triples_i_list_aux_147 triples_i_aux_147].
    rewrite length_app, Nat2Z.inj_add, IHfuel, triples_j_list_length_147.
    reflexivity.
Qed.

Lemma triples_list_length_147 : forall n,
  0 <= n ->
  Z.of_nat (length (triples_list_147 n)) = triples_i_147 n (n + 1).
Proof.
  intros n Hn.
  unfold triples_list_147, triples_i_147.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by (f_equal; lia).
  apply triples_i_list_length_147.
Qed.

Lemma triples_k_list_sound_147 : forall n i j fuel t,
  1 <= i < j ->
  j + Z.of_nat fuel <= n ->
  In t (triples_k_list_aux_147 n i j fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_k_list_aux_147]; intros t Hij Hfuel Hin; try contradiction.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
  - rewrite in_app_iff in Hin. destruct Hin as [Hin | [Heq | []]].
    + eapply IHfuel; eauto; lia.
    + subst t. apply triple_good_bool_valid_147; try lia; exact Hgood.
  - eapply IHfuel; eauto; lia.
Qed.

Lemma triples_j_list_sound_147 : forall n i fuel t,
  1 <= i ->
  i + Z.of_nat fuel <= n ->
  In t (triples_j_list_aux_147 n i fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros t Hi Hfuel Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - eapply IHfuel; eauto; lia.
  - eapply (triples_k_list_sound_147 n i (i + 1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) t); eauto; try lia.
Qed.

Lemma triples_i_list_sound_147 : forall n fuel t,
  Z.of_nat fuel <= n ->
  In t (triples_i_list_aux_147 n fuel) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros t Hfuel Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - eapply IHfuel; eauto; lia.
  - eapply (triples_j_list_sound_147 n (1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) t); eauto; try lia.
Qed.

Lemma triples_list_sound_147 : forall n t,
  0 <= n ->
  In t (triples_list_147 n) ->
  let '(a,b,c) := t in is_valid_triple (Z.to_nat n) a b c.
Proof.
  intros n t Hn Hin.
  unfold triples_list_147 in Hin.
  eapply triples_i_list_sound_147; eauto.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_k_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_k_list_aux_147 n i j (Z.to_nat (n - j))).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat (n - j)) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n - j) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= k - (j + 1) < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert k Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros k Hk Hgood Hrange; cbn [triples_k_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (k - (j + 1)) (Z.of_nat fuel)).
    + assert (k = j + 1 + Z.of_nat fuel) by lia. subst k.
      rewrite Hgood. rewrite in_app_iff. right; left.
      f_equal; rewrite Z2Nat.id by lia; reflexivity.
	    + destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)).
	      * rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
	      * apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_j_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_j_list_aux_147 n i (Z.to_nat (n - i))).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat (n - i)) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n - i) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= j - (i + 1) < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert j k Hij Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros j k Hij Hk Hgood Hrange; cbn [triples_j_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (j - (i + 1)) (Z.of_nat fuel)).
    + assert (j = i + 1 + Z.of_nat fuel) by lia. subst j.
      rewrite in_app_iff. right.
      replace (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) with
        (Z.to_nat (n - (i + 1 + Z.of_nat fuel))) by (f_equal; lia).
      apply triples_k_list_complete_147; try lia; exact Hgood.
    + rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_i_list_complete_147 : forall n i j k,
  1 <= i < j ->
  j < k <= n ->
  triple_good_bool_147 i j k = true ->
  In (Z.to_nat i, Z.to_nat j, Z.to_nat k)
     (triples_i_list_aux_147 n (Z.to_nat n)).
Proof.
  intros n i j k Hij Hk Hgood.
  remember (Z.to_nat n) as fuel eqn:Hfuel.
  assert (HfuelZ : Z.of_nat fuel = n) by (subst fuel; rewrite Z2Nat.id by lia; lia).
  assert (Hrange : 0 <= i - 1 < Z.of_nat fuel) by lia.
  clear Hfuel HfuelZ.
  revert i j k Hij Hk Hgood Hrange.
  induction fuel as [|fuel IHfuel]; intros i j k Hij Hk Hgood Hrange; cbn [triples_i_list_aux_147].
  - lia.
  - destruct (Z.eq_dec (i - 1) (Z.of_nat fuel)).
    + assert (i = 1 + Z.of_nat fuel) by lia. subst i.
      rewrite in_app_iff. right.
      replace (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) with
        (Z.to_nat (n - (1 + Z.of_nat fuel))) by (f_equal; lia).
      apply triples_j_list_complete_147; try lia; exact Hgood.
    + rewrite in_app_iff. left. apply IHfuel; try lia; exact Hgood.
Qed.

Lemma triples_list_complete_147 : forall n i j k,
  is_valid_triple (Z.to_nat n) i j k ->
  0 <= n ->
  In (i,j,k) (triples_list_147 n).
Proof.
  intros n i j k Hvalid Hn.
  destruct Hvalid as [Hi [Hij [Hjk [Hkn Hmod]]]].
  unfold triples_list_147.
  replace i with (Z.to_nat (Z.of_nat i)) by (rewrite Nat2Z.id; reflexivity).
  replace j with (Z.to_nat (Z.of_nat j)) by (rewrite Nat2Z.id; reflexivity).
  replace k with (Z.to_nat (Z.of_nat k)) by (rewrite Nat2Z.id; reflexivity).
  apply triples_i_list_complete_147.
  - split.
    + lia.
    + apply Nat2Z.inj_lt; exact Hij.
  - split.
    + apply Nat2Z.inj_lt; exact Hjk.
    + apply Nat2Z.inj_le in Hkn. rewrite Z2Nat.id in Hkn by lia. exact Hkn.
  - apply (is_valid_triple_good_bool_147 n i j k); try lia.
    repeat split; try lia; exact Hmod.
Qed.

Lemma triples_k_list_in_range_147 : forall n i j fuel a b c,
  1 <= i < j ->
  In (a,b,c) (triples_k_list_aux_147 n i j fuel) ->
  a = Z.to_nat i /\ b = Z.to_nat j /\ j + 1 <= Z.of_nat c <= j + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_k_list_aux_147]; intros a b c Hij Hin; try contradiction.
  destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
  - rewrite in_app_iff in Hin. destruct Hin as [Hin | [Heq | []]].
    + specialize (IHfuel _ _ _ Hij Hin) as [? [? ?]]. repeat split; try assumption; lia.
    + inversion Heq; subst. repeat split; try reflexivity; rewrite Z2Nat.id by lia; lia.
  - specialize (IHfuel _ _ _ Hij Hin) as [? [? ?]]. repeat split; try assumption; lia.
Qed.

Lemma triples_k_list_NoDup_147 : forall n i j fuel,
  1 <= i < j ->
  NoDup (triples_k_list_aux_147 n i j fuel).
Proof.
  intros n i j fuel Hij.
  induction fuel as [|fuel IHfuel].
  - cbn [triples_k_list_aux_147]. constructor.
  - cbn [triples_k_list_aux_147].
    destruct (triple_good_bool_147 i j (j + 1 + Z.of_nat fuel)) eqn:Hgood.
    + apply NoDup_app.
      * apply IHfuel.
      * constructor; [intro H; contradiction|constructor].
      * intros [[a b] c] Hin Hnew.
      destruct Hnew as [Heq | []]. inversion Heq; subst.
      pose proof (triples_k_list_in_range_147 n i j fuel _ _ _ Hij Hin) as [_ [_ Hc]].
      rewrite Z2Nat.id in Hc by lia. lia.
    + apply IHfuel.
Qed.

Lemma triples_j_list_in_range_147 : forall n i fuel a b c,
  1 <= i ->
  In (a,b,c) (triples_j_list_aux_147 n i fuel) ->
  a = Z.to_nat i /\ i + 1 <= Z.of_nat b <= i + Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros a b c Hi Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - specialize (IHfuel _ _ _ Hi Hin) as [? ?]. split; try assumption; lia.
  - pose proof (triples_k_list_in_range_147 n i (i + 1 + Z.of_nat fuel)
      (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin)
      as [Ha [Hb Hc]].
    subst b. split; try assumption. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_j_list_NoDup_147 : forall n i fuel,
  1 <= i ->
  i + Z.of_nat fuel <= n ->
  NoDup (triples_j_list_aux_147 n i fuel).
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_j_list_aux_147]; intros Hi Hfuel.
  - constructor.
  - apply NoDup_app.
    + apply IHfuel; lia.
    + apply triples_k_list_NoDup_147; lia.
    + intros [[a b] c] Hin1 Hin2.
      pose proof (triples_j_list_in_range_147 n i fuel a b c Hi Hin1) as [_ Hb1].
      pose proof (triples_k_list_in_range_147 n i (i + 1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (i + 1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin2)
        as [_ [Hb2 _]].
      subst b. rewrite Z2Nat.id in Hb1 by lia. lia.
Qed.

Lemma triples_i_list_in_range_147 : forall n fuel a b c,
  In (a,b,c) (triples_i_list_aux_147 n fuel) ->
  1 <= Z.of_nat a <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros a b c Hin; try contradiction.
  rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - pose proof (IHfuel _ _ _ Hin). lia.
  - pose proof (triples_j_list_in_range_147 n (1 + Z.of_nat fuel)
      (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin)
      as [Ha _].
    subst a. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma triples_i_list_NoDup_147 : forall n fuel,
  Z.of_nat fuel <= n ->
  NoDup (triples_i_list_aux_147 n fuel).
Proof.
  induction fuel as [|fuel IHfuel]; cbn [triples_i_list_aux_147]; intros Hfuel.
  - constructor.
  - apply NoDup_app.
    + apply IHfuel; lia.
    + apply triples_j_list_NoDup_147; try lia.
    + intros [[a b] c] Hin1 Hin2.
      pose proof (triples_i_list_in_range_147 n fuel a b c Hin1) as Ha1.
      pose proof (triples_j_list_in_range_147 n (1 + Z.of_nat fuel)
        (Z.to_nat (n + 1 - (1 + Z.of_nat fuel + 1))) a b c ltac:(lia) Hin2)
        as [Ha2 _].
      subst a. rewrite Z2Nat.id in Ha1 by lia. lia.
Qed.

Lemma triples_list_NoDup_147 : forall n,
  0 <= n ->
  NoDup (triples_list_147 n).
Proof.
  intros n Hn.
  unfold triples_list_147.
  apply triples_i_list_NoDup_147.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma problem_147_spec_z_of_count : forall n,
  1 <= n <= 1004 ->
  problem_147_pre_z n ->
  problem_147_spec_z n (triples_i_147 n (n + 1)).
Proof.
  intros n Hn Hpre.
  unfold problem_147_spec_z.
  split; [lia|].
  split.
  - apply triples_i_nonneg_147.
  - unfold problem_147_spec.
    exists (triples_list_147 n).
    repeat split.
    + intros ijk Hin.
      destruct ijk as [[i j] k].
      apply (triples_list_sound_147 n (i, j, k)); try lia; exact Hin.
    + intros i j k Hvalid.
      apply triples_list_complete_147; try lia; exact Hvalid.
    + apply triples_list_NoDup_147; lia.
    + apply Nat2Z.inj.
      rewrite triples_list_length_147 by lia.
      rewrite Z2Nat.id by apply triples_i_nonneg_147.
      reflexivity.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Ltac solve_safety_147 :=
  left; pre_process; andp_cancel; try nia.

Ltac solve_entail_147 :=
  left; pre_process; andp_cancel; auto; try lia; try nia.

Lemma proof_of_get_matrix_triples_safety_wit_10 : get_matrix_triples_safety_wit_10.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_11 : get_matrix_triples_safety_wit_11.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_12 : get_matrix_triples_safety_wit_12.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_13 : get_matrix_triples_safety_wit_13.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_14 : get_matrix_triples_safety_wit_14.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_15 : get_matrix_triples_safety_wit_15.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_16 : get_matrix_triples_safety_wit_16.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_17 : get_matrix_triples_safety_wit_17.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_18 : get_matrix_triples_safety_wit_18.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_19 : get_matrix_triples_safety_wit_19.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_20 : get_matrix_triples_safety_wit_20.
Proof. solve_safety_147. Qed.

Lemma proof_of_get_matrix_triples_safety_wit_26 : get_matrix_triples_safety_wit_26.
Proof.
  left; pre_process.
  pose proof (triples_partial_bound_147 n_pre i j k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  andp_cancel; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_1 : get_matrix_triples_entail_wit_1.
Proof.
  left; pre_process.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_2 : get_matrix_triples_entail_wit_2.
Proof.
  left; pre_process.
  unfold triples_j_147.
  replace (Z.to_nat (i + 1 - (i + 1))) with 0%nat by lia.
  simpl.
  andp_cancel; auto; lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_3 : get_matrix_triples_entail_wit_3.
Proof.
  left; pre_process.
  unfold triples_k_147.
  replace (Z.to_nat (j + 1 - (j + 1))) with 0%nat by lia.
  simpl.
  andp_cancel; auto; lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_4_1 : get_matrix_triples_entail_wit_4_1.
Proof.
  left; pre_process.
  assert (Hgood : triple_good_bool_147 i j k = true).
  {
    unfold triple_good_bool_147, triple_value_147.
    apply Z.eqb_eq.
    exact PreH1.
  }
  rewrite (triples_k_step_good_147 n_pre i j k ltac:(lia) Hgood).
  pose proof (triples_partial_bound_147 n_pre i j k ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_4_2 : get_matrix_triples_entail_wit_4_2.
Proof.
  left; pre_process.
  assert (Hbad : triple_good_bool_147 i j k = false).
  {
    unfold triple_good_bool_147, triple_value_147.
    apply Z.eqb_neq.
    exact PreH1.
  }
  rewrite (triples_k_step_bad_147 n_pre i j k ltac:(lia) Hbad).
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_5 : get_matrix_triples_entail_wit_5.
Proof.
  left; pre_process.
  assert (k = n_pre + 1) by lia.
  subst k.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_6 : get_matrix_triples_entail_wit_6.
Proof.
  left; pre_process.
  rewrite triples_j_step_147 by lia.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_7 : get_matrix_triples_entail_wit_7.
Proof.
  left; pre_process.
  assert (j = n_pre + 1) by lia.
  subst j.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_8 : get_matrix_triples_entail_wit_8.
Proof.
  left; pre_process.
  rewrite triples_i_step_147 by lia.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_entail_wit_9 : get_matrix_triples_entail_wit_9.
Proof.
  left; pre_process.
  assert (i = n_pre + 1) by lia.
  subst i.
  andp_cancel; auto; try lia.
Qed.

Lemma proof_of_get_matrix_triples_return_wit_1 : get_matrix_triples_return_wit_1.
Proof.
  left; pre_process.
  andp_cancel; auto; try lia.
  subst count.
  apply problem_147_spec_z_of_count; auto; lia.
Qed.
