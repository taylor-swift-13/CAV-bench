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
From SimpleC.EE.CAV.ground_truth_p151_double_the_difference Require Import p151_double_the_difference_goal.
From SimpleC.EE.CAV.ground_truth_p151_double_the_difference Require Import p151_double_the_difference_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p151_double_the_difference.
Local Open Scope sac.

Import ListNotations.

Lemma firstn_succ_nth_151 :
  forall (n : nat) (xs : list Z),
    (n < List.length xs)%nat ->
    firstn (S n) xs = firstn n xs ++ [nth n xs 0].
Proof.
  induction n as [| n IH]; intros xs Hlt.
  - destruct xs; [simpl in Hlt; lia | reflexivity].
  - destruct xs as [| x xs]; [simpl in Hlt; lia |].
    change (x :: firstn (S n) xs =
            x :: (firstn n xs ++ [nth n xs 0])).
    f_equal. apply IH. simpl in Hlt. lia.
Qed.

Lemma firstn_Z_succ_151 :
  forall xs i,
    0 <= i -> i < Zlength xs ->
    firstn (Z.to_nat (i + 1)) xs =
    firstn (Z.to_nat i) xs ++ [Znth i xs 0].
Proof.
  intros xs i Hi Hlt.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hsucc. apply firstn_succ_nth_151.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. exact Hlt.
Qed.

Lemma sum_contributions_151_app : forall xs ys,
  sum_contributions_151 (xs ++ ys) =
  sum_contributions_151 xs + sum_contributions_151 ys.
Proof.
  induction xs as [| x xs IH]; intros ys; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma odd_of_mod_nonzero_151 : forall x,
  x mod 2 <> 0 -> Z.odd x = true.
Proof.
  intros x Hmod. pose proof (Zmod_odd x) as Hodd.
  destruct (Z.odd x) eqn:E.
  - reflexivity.
  - simpl in Hodd. contradiction.
Qed.

Lemma even_of_mod_zero_151 : forall x,
  x mod 2 = 0 -> Z.odd x = false.
Proof.
  intros x Hmod. pose proof (Zmod_odd x) as Hodd.
  destruct (Z.odd x) eqn:E.
  - simpl in Hodd. lia.
  - reflexivity.
Qed.

Lemma prefix_odd_151 : forall input i sum,
  0 <= i -> i < Zlength input ->
  0 < Znth i input 0 -> Z.rem (Znth i input 0) 2 <> 0 ->
  problem_151_prefix_z input i sum ->
  problem_151_prefix_z input (i + 1)
    (sum + Znth i input 0 * Znth i input 0).
Proof.
  intros input i sum Hi Hlt Hpos Hodd Hprefix.
  unfold problem_151_prefix_z in *.
  rewrite firstn_Z_succ_151 by lia.
  rewrite sum_contributions_151_app. simpl.
  unfold contribution_151_z.
  assert (Htest : (0 <? Znth i input 0) = true) by
    (apply Z.ltb_lt; exact Hpos).
  rewrite Htest.
  assert (Hmod : Znth i input 0 mod 2 <> 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact Hodd. }
  rewrite odd_of_mod_nonzero_151 by exact Hmod.
  simpl. lia.
Qed.

Lemma prefix_nonpositive_151 : forall input i sum,
  0 <= i -> i < Zlength input -> Znth i input 0 <= 0 ->
  problem_151_prefix_z input i sum ->
  problem_151_prefix_z input (i + 1) sum.
Proof.
  intros input i sum Hi Hlt Hnonpos Hprefix.
  unfold problem_151_prefix_z in *.
  rewrite firstn_Z_succ_151 by lia.
  rewrite sum_contributions_151_app. simpl.
  unfold contribution_151_z.
  assert (Htest : (0 <? Znth i input 0) = false) by
    (apply Z.ltb_ge; lia).
  rewrite Htest. simpl. lia.
Qed.

Lemma prefix_even_151 : forall input i sum,
  0 <= i -> i < Zlength input -> 0 < Znth i input 0 ->
  Z.rem (Znth i input 0) 2 = 0 ->
  problem_151_prefix_z input i sum ->
  problem_151_prefix_z input (i + 1) sum.
Proof.
  intros input i sum Hi Hlt Hpos Heven Hprefix.
  unfold problem_151_prefix_z in *.
  rewrite firstn_Z_succ_151 by lia.
  rewrite sum_contributions_151_app. simpl.
  unfold contribution_151_z.
  assert (Htest : (0 <? Znth i input 0) = true) by
    (apply Z.ltb_lt; exact Hpos).
  rewrite Htest.
  assert (Hmod : Znth i input 0 mod 2 = 0).
  { rewrite <- Z.rem_mod_nonneg by lia. exact Heven. }
  rewrite even_of_mod_zero_151 by exact Hmod.
  simpl. lia.
Qed.

Lemma proof_of_double_the_difference_safety_wit_7 : double_the_difference_safety_wit_7.
Proof.
  unfold double_the_difference_safety_wit_7. left.
  intros. Intros.
  assert (Hnext : problem_151_prefix_z input (i + 1)
      (sum + Znth i input 0 * Znth i input 0)).
  { apply prefix_odd_151.
    - lia.
    - lia.
    - lia.
    - exact PreH1.
    - exact PreH11. }
  pose proof PreH10 as Hbounds.
  destruct Hbounds as [_ Hbounds].
  specialize (Hbounds (i + 1)).
  assert (Hrange : 0 <= i + 1 <= Z.of_nat (length input)).
  { rewrite <- Zlength_correct. lia. }
  specialize (Hbounds Hrange).
  unfold problem_151_prefix_z in Hnext.
  rewrite <- Hnext in Hbounds.
  entailer!.
Qed.

Lemma proof_of_double_the_difference_safety_wit_8 : double_the_difference_safety_wit_8.
Proof.
  unfold double_the_difference_safety_wit_8. left.
  intros. Intros.
  destruct PreH10 as [Hall _].
  apply Forall_forall with (x := Znth i input 0) in Hall.
  2: {
    unfold Znth. apply nth_In.
    apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  entailer!; nia.
Qed.

Lemma proof_of_double_the_difference_entail_wit_1 : double_the_difference_entail_wit_1.
Proof.
  unfold double_the_difference_entail_wit_1. left.
  intros. Intros. entailer!.
Qed.

Lemma proof_of_double_the_difference_entail_wit_2_1 : double_the_difference_entail_wit_2_1.
Proof.
  unfold double_the_difference_entail_wit_2_1. left.
  intros. Intros.
  assert (Hnext : problem_151_prefix_z input (i + 1)
      (sum + Znth i input 0 * Znth i input 0)).
  { apply prefix_odd_151.
    - lia.
    - lia.
    - lia.
    - exact PreH1.
    - exact PreH11. }
  pose proof PreH10 as Hbounds.
  destruct Hbounds as [_ Hbounds].
  specialize (Hbounds (i + 1)).
  assert (Hrange : 0 <= i + 1 <= Z.of_nat (length input)).
  { rewrite <- Zlength_correct. lia. }
  specialize (Hbounds Hrange).
  unfold problem_151_prefix_z in Hnext.
  rewrite <- Hnext in Hbounds.
  entailer!; lia.
Qed.

Lemma proof_of_double_the_difference_entail_wit_2_2 : double_the_difference_entail_wit_2_2.
Proof.
  unfold double_the_difference_entail_wit_2_2. left.
  intros. Intros. entailer!.
  apply prefix_nonpositive_151.
  - lia.
  - lia.
  - lia.
  - exact PreH10.
Qed.

Lemma proof_of_double_the_difference_entail_wit_2_3 : double_the_difference_entail_wit_2_3.
Proof.
  unfold double_the_difference_entail_wit_2_3. left.
  intros. Intros. entailer!.
  apply prefix_even_151.
  - lia.
  - lia.
  - lia.
  - exact PreH1.
  - exact PreH11.
Qed.

Lemma proof_of_double_the_difference_return_wit_1 : double_the_difference_return_wit_1.
Proof.
  unfold double_the_difference_return_wit_1. left.
  intros. Intros. entailer!.
  unfold problem_151_spec_z, problem_151_prefix_z in *.
  assert (Hi : i = lst_size_pre) by lia. subst i.
  assert (Hlen : Z.to_nat lst_size_pre = List.length input).
  { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  rewrite Hlen, firstn_all in PreH9. exact PreH9.
Qed.
