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
From SimpleC.EE.CAV.ground_truth_p035_max_element Require Import p035_max_element_goal.
From SimpleC.EE.CAV.ground_truth_p035_max_element Require Import p035_max_element_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p035_max_element.
Local Open Scope sac.

Import ListNotations.

Lemma firstn_succ_nth_35 :
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

Lemma firstn_Z_succ_35 :
  forall xs i,
    0 <= i -> i < Zlength xs ->
    firstn (Z.to_nat (i + 1)) xs =
    firstn (Z.to_nat i) xs ++ [Znth i xs 0].
Proof.
  intros xs i Hi Hlt.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hsucc. apply firstn_succ_nth_35.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. exact Hlt.
Qed.

Lemma proof_of_max_element_entail_wit_1 : max_element_entail_wit_1.
Proof.
  unfold max_element_entail_wit_1.
  left. intros. Intros. entailer!.
  unfold problem_35_prefix, Znth.
  destruct xs as [| x xs].
  - unfold problem_35_pre in PreH4. contradiction.
  - simpl. split.
    + left. reflexivity.
    + intros y [Hy | []]. subst y. lia.
Qed.

Lemma proof_of_max_element_entail_wit_2_1 : max_element_entail_wit_2_1.
Proof.
  unfold max_element_entail_wit_2_1.
  left. intros. Intros. entailer!.
  unfold problem_35_prefix in *.
  rewrite firstn_Z_succ_35 by lia.
  destruct PreH8 as [Hcur Hmax].
  split.
  - apply in_or_app. right. left. reflexivity.
  - intros x Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | [Hx | []]].
    + specialize (Hmax x Hx). lia.
    + subst x. lia.
Qed.

Lemma proof_of_max_element_entail_wit_2_2 : max_element_entail_wit_2_2.
Proof.
  unfold max_element_entail_wit_2_2.
  left. intros. Intros. entailer!.
  unfold problem_35_prefix in *.
  rewrite firstn_Z_succ_35 by lia.
  destruct PreH8 as [Hcur Hmax].
  split.
  - apply in_or_app. left. exact Hcur.
  - intros x Hx. apply in_app_or in Hx.
    destruct Hx as [Hx | [Hx | []]].
    + apply Hmax. exact Hx.
    + subst x. lia.
Qed.

Lemma proof_of_max_element_return_wit_1 : max_element_return_wit_1.
Proof.
  unfold max_element_return_wit_1.
  left. intros. Intros. entailer!.
  unfold problem_35_prefix in PreH7.
  unfold problem_35_spec.
  assert (Hi : i = l_size_pre) by lia. subst i.
  assert (Hlen : Z.to_nat l_size_pre = List.length xs).
  { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  rewrite Hlen, firstn_all in PreH7.
  exact PreH7.
Qed.
