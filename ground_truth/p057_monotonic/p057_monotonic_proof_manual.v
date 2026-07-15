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
From SimpleC.EE.CAV.ground_truth_p057_monotonic Require Import p057_monotonic_goal.
From SimpleC.EE.CAV.ground_truth_p057_monotonic Require Import p057_monotonic_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p057_monotonic.
Local Open Scope sac.

Lemma nondecreasing_step_57 : forall input i,
  1 <= i ->
  nondecreasing_57 input (i + 1) <->
  nondecreasing_57 input i /\
  Znth (i - 1) input 0 <= Znth i input 0.
Proof.
  intros input i Hi. split.
  - intros H. split.
    + intros j Hj. apply H. lia.
    + apply H. lia.
  - intros [Hold Hedge] j Hj.
    destruct (Z_lt_ge_dec j i).
    + apply Hold. lia.
    + assert (j = i) by lia. subst j. exact Hedge.
Qed.

Lemma nonincreasing_step_57 : forall input i,
  1 <= i ->
  nonincreasing_57 input (i + 1) <->
  nonincreasing_57 input i /\
  Znth i input 0 <= Znth (i - 1) input 0.
Proof.
  intros input i Hi. split.
  - intros H. split.
    + intros j Hj. apply H. lia.
    + apply H. lia.
  - intros [Hold Hedge] j Hj.
    destruct (Z_lt_ge_dec j i).
    + apply Hold. lia.
    + assert (j = i) by lia. subst j. exact Hedge.
Qed.

Lemma prefix_rise_57 : forall input i incr decr,
  1 <= i -> Znth (i - 1) input 0 < Znth i input 0 ->
  problem_57_prefix_z input i incr decr ->
  problem_57_prefix_z input (i + 1) incr 0.
Proof.
  intros input i incr decr Hi Hedge Hprefix.
  unfold problem_57_prefix_z in *. destruct Hprefix as [Hinc Hdec].
  split.
  - destruct Hinc as [[-> Hnd] | [-> Hnnd]].
    + left. split; [reflexivity|].
      apply (proj2 (nondecreasing_step_57 input i Hi)).
      split; [exact Hnd | lia].
    + right. split; [reflexivity|]. intros Hnew.
      apply Hnnd. apply (proj1 (nondecreasing_step_57 input i Hi)) in Hnew.
      tauto.
  - right. split; [reflexivity|]. intros Hnew.
    apply (proj1 (nonincreasing_step_57 input i Hi)) in Hnew. lia.
Qed.

Lemma prefix_fall_57 : forall input i incr decr,
  1 <= i -> Znth i input 0 < Znth (i - 1) input 0 ->
  problem_57_prefix_z input i incr decr ->
  problem_57_prefix_z input (i + 1) 0 decr.
Proof.
  intros input i incr decr Hi Hedge Hprefix.
  unfold problem_57_prefix_z in *. destruct Hprefix as [Hinc Hdec].
  split.
  - right. split; [reflexivity|]. intros Hnew.
    apply (proj1 (nondecreasing_step_57 input i Hi)) in Hnew. lia.
  - destruct Hdec as [[-> Hni] | [-> Hnni]].
    + left. split; [reflexivity|].
      apply (proj2 (nonincreasing_step_57 input i Hi)).
      split; [exact Hni | lia].
    + right. split; [reflexivity|]. intros Hnew.
      apply Hnni. apply (proj1 (nonincreasing_step_57 input i Hi)) in Hnew.
      tauto.
Qed.

Lemma prefix_equal_57 : forall input i incr decr,
  1 <= i -> Znth i input 0 = Znth (i - 1) input 0 ->
  problem_57_prefix_z input i incr decr ->
  problem_57_prefix_z input (i + 1) incr decr.
Proof.
  intros input i incr decr Hi Hedge Hprefix.
  unfold problem_57_prefix_z in *. destruct Hprefix as [Hinc Hdec].
  split.
  - destruct Hinc as [[-> Hnd] | [-> Hnnd]].
    + left. split; [reflexivity|].
      apply (proj2 (nondecreasing_step_57 input i Hi)).
      split; [exact Hnd | lia].
    + right. split; [reflexivity|]. intros Hnew.
      apply Hnnd. apply (proj1 (nondecreasing_step_57 input i Hi)) in Hnew.
      tauto.
  - destruct Hdec as [[-> Hni] | [-> Hnni]].
    + left. split; [reflexivity|].
      apply (proj2 (nonincreasing_step_57 input i Hi)).
      split; [exact Hni | lia].
    + right. split; [reflexivity|]. intros Hnew.
      apply Hnni. apply (proj1 (nonincreasing_step_57 input i Hi)) in Hnew.
      tauto.
Qed.

Lemma proof_of_monotonic_entail_wit_1 : monotonic_entail_wit_1.
Proof.
  unfold monotonic_entail_wit_1. left.
  intros. Intros. entailer!.
  unfold problem_57_prefix_z. split; left; split; try reflexivity.
  - intros j Hj. lia.
  - intros j Hj. lia.
Qed.

Lemma proof_of_monotonic_entail_wit_2_1 : monotonic_entail_wit_2_1.
Proof.
  unfold monotonic_entail_wit_2_1. left.
  intros. Intros. entailer!.
  apply (prefix_rise_57 input i incr decr).
  - lia.
  - lia.
  - exact PreH9.
Qed.

Lemma proof_of_monotonic_entail_wit_2_2 : monotonic_entail_wit_2_2.
Proof.
  unfold monotonic_entail_wit_2_2. left.
  intros. Intros. entailer!.
  apply (prefix_fall_57 input i incr decr).
  - lia.
  - lia.
  - exact PreH9.
Qed.

Lemma proof_of_monotonic_entail_wit_2_3 : monotonic_entail_wit_2_3.
Proof.
  unfold monotonic_entail_wit_2_3. left.
  intros. Intros. entailer!.
  apply (prefix_equal_57 input i incr decr).
  - lia.
  - lia.
  - exact PreH9.
Qed.

Lemma proof_of_monotonic_return_wit_1 : monotonic_return_wit_1.
Proof.
  unfold monotonic_return_wit_1. left.
  intros. Intros. entailer!.
  unfold problem_57_spec_z.
  assert (Hi : i = Zlength input) by lia. subst i.
  unfold problem_57_prefix_z in PreH9.
  destruct PreH9 as [[[Hincr Hnd] | [Hincr Hnnd]]
                     [[Hdecr Hni] | [Hdecr Hnni]]]; try lia.
  right. split; [reflexivity|]. tauto.
Qed.

Lemma proof_of_monotonic_return_wit_2 : monotonic_return_wit_2.
Proof.
  unfold monotonic_return_wit_2. left.
  intros. Intros. entailer!.
  unfold problem_57_spec_z.
  assert (Hi : i = Zlength input) by lia. subst i.
  unfold problem_57_prefix_z in PreH8.
  destruct PreH8 as [[[Hincr Hnd] | [Hincr Hnnd]] Hdecr]; try lia.
  left. split; [reflexivity|]. left. exact Hnd.
Qed.

Lemma proof_of_monotonic_return_wit_3 : monotonic_return_wit_3.
Proof.
  unfold monotonic_return_wit_3. left.
  intros. Intros. entailer!.
  unfold problem_57_spec_z.
  assert (Hi : i = Zlength input) by lia. subst i.
  unfold problem_57_prefix_z in PreH9.
  destruct PreH9 as [Hincr [[Hdecr Hni] | [Hdecr Hnni]]]; try lia.
  left. split; [reflexivity|]. right. exact Hni.
Qed.
