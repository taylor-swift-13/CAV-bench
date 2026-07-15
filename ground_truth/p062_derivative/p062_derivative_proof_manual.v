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
From SimpleC.EE.CAV.ground_truth_p062_derivative Require Import p062_derivative_goal.
From SimpleC.EE.CAV.ground_truth_p062_derivative Require Import p062_derivative_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p062_derivative.
Local Open Scope sac.

Import ListNotations.

Lemma firstn_succ_nth_62 : forall (n : nat) (xs : list Z),
  (n < length xs)%nat ->
  firstn (S n) xs = firstn n xs ++ [nth n xs 0].
Proof.
  induction n as [|n IH]; intros xs Hlt.
  - destruct xs; [simpl in Hlt; lia | reflexivity].
  - destruct xs as [|x xs]; [simpl in Hlt; lia |].
    simpl. f_equal. apply IH. simpl in Hlt. lia.
Qed.

Lemma firstn_tail_step_62 : forall input i,
  1 <= i < Zlength input ->
  firstn (Z.to_nat i) (tl input) =
  firstn (Z.to_nat (i - 1)) (tl input) ++ [Znth i input 0].
Proof.
  intros input i Hi.
  destruct input as [|x xs].
  - change (1 <= i < 0) in Hi. lia.
  -
  simpl.
  assert (Hnat : Z.to_nat i = S (Z.to_nat (i - 1))).
  { replace i with ((i - 1) + 1) at 1 by lia.
    rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hnat. rewrite firstn_succ_nth_62.
  + unfold Znth. simpl.
    replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by (symmetry; exact Hnat).
    reflexivity.
  + apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. rewrite Zlength_cons in Hi. lia.
Qed.

Lemma derivative_from_62_app_one : forall xs k x,
  derivative_from_62 k (xs ++ [x]) =
  derivative_from_62 k xs ++ [(k + Z.of_nat (length xs)) * x].
Proof.
  induction xs as [|y ys IH]; intros k x; simpl.
  - f_equal. lia.
  - f_equal. rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma prefix_step_62 : forall input i output,
  1 <= i < Zlength input ->
  problem_62_prefix_z input i output ->
  problem_62_prefix_z input (i + 1)
    (output ++ [i * Znth i input 0]).
Proof.
  intros input i output Hi Hprefix.
  unfold problem_62_prefix_z in *.
  assert (Hnat : Z.to_nat (i + 1 - 1) = Z.to_nat i) by
    (f_equal; lia).
  rewrite Hnat, firstn_tail_step_62 by exact Hi.
  rewrite derivative_from_62_app_one.
  rewrite <- Hprefix.
  f_equal. f_equal.
  rewrite firstn_length.
  assert (Hle : (Z.to_nat (i - 1) <= length (tl input))%nat).
  { destruct input as [|x xs].
    - rewrite Zlength_nil in Hi. lia.
    - simpl. apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. rewrite Zlength_cons in Hi. lia. }
  rewrite Nat.min_l by exact Hle.
  rewrite Z2Nat.id by lia. lia.
Qed.

Lemma prefix_final_62 : forall input i output,
  1 <= i -> i = Zlength input ->
  problem_62_prefix_z input i output ->
  problem_62_spec_z input output.
Proof.
  intros input i output Hi Hlen Hprefix.
  unfold problem_62_prefix_z in Hprefix.
  unfold problem_62_spec_z, derivative_62.
  rewrite Hprefix.
  destruct input as [|x xs].
  - rewrite Zlength_nil in Hlen. lia.
  - simpl.
    assert (Hnat : Z.to_nat (i - 1) = length xs).
    { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
      rewrite <- Zlength_correct. rewrite Zlength_cons in Hlen. lia. }
    rewrite Hnat, firstn_all. reflexivity.
Qed.

Lemma proof_of_derivative_safety_wit_4 : derivative_safety_wit_4.
Proof.
  unfold derivative_safety_wit_4. left.
  intros. Intros.
  destruct PreH6 as [_ Hbound].
  specialize (Hbound i ltac:(lia)). destruct Hbound.
  entailer!.
Qed.

Lemma proof_of_derivative_entail_wit_1 : derivative_entail_wit_1.
Proof.
  unfold derivative_entail_wit_1. left.
  intros. Intros.
  assert (Hprefix : problem_62_prefix_z input 1 (@nil Z)).
  { unfold problem_62_prefix_z. replace (1 - 1) with 0 by lia. reflexivity. }
  Exists (@nil Z). entailer!.
  rewrite IntArray.seg_empty.
  sep_apply_l_atomic
    (IntArray.undef_full_to_undef_seg out_pre (xs_size_pre - 1)).
  cancel. entailer!.
Qed.

Lemma proof_of_derivative_entail_wit_2 : derivative_entail_wit_2.
Proof.
  unfold derivative_entail_wit_2. right.
  intros. Intros.
  assert (Hprefix : problem_62_prefix_z input (i + 1)
      (output_2 ++ [i * Znth i input 0])).
  { apply prefix_step_62.
    - lia.
    - exact PreH8. }
  assert (Houtlen : Zlength (output_2 ++ [i * Znth i input 0]) =
                    i + 1 - 1).
  { rewrite Zlength_app, PreH7, Zlength_cons, Zlength_nil. lia. }
  replace (i - 1 + 1) with (i + 1 - 1) in * by lia.
  Exists (output_2 ++ [i * Znth i input 0]). entailer!.
Qed.

Lemma proof_of_derivative_return_wit_1 : derivative_return_wit_1.
Proof.
  unfold derivative_return_wit_1. left.
  intros. Intros. Exists output_2.
  assert (Hi : i = xs_size_pre) by lia. subst i.
  assert (Hspec : problem_62_spec_z input output_2).
  { apply prefix_final_62 with (i := xs_size_pre).
    - lia.
    - symmetry. exact PreH5.
    - exact PreH8. }
  rewrite IntArray.undef_seg_empty by lia.
  sep_apply_l_atomic
    (IntArray.seg_to_full out_pre 0 (xs_size_pre - 1) output_2).
  replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
  replace (xs_size_pre - 1 - 0) with (xs_size_pre - 1) by lia.
  entailer!.
Qed.
