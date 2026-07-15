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
From SimpleC.EE.CAV.ground_truth_p030_get_positive Require Import p030_get_positive_goal.
From SimpleC.EE.CAV.ground_truth_p030_get_positive Require Import p030_get_positive_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p030_get_positive.
Local Open Scope sac.

Import ListNotations.

Lemma firstn_succ_nth_30 :
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

Lemma firstn_Z_succ_30 :
  forall xs i,
    0 <= i -> i < Zlength xs ->
    firstn (Z.to_nat (i + 1)) xs =
    firstn (Z.to_nat i) xs ++ [Znth i xs 0].
Proof.
  intros xs i Hi Hlt.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite Hsucc. apply firstn_succ_nth_30.
  apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct. exact Hlt.
Qed.

Lemma filter_positive_30_app : forall xs ys,
  filter_positive_30 (xs ++ ys) =
  filter_positive_30 xs ++ filter_positive_30 ys.
Proof.
  induction xs as [| x xs IH]; intros ys; simpl.
  - reflexivity.
  - destruct (Z.ltb 0 x); simpl; rewrite IH; reflexivity.
Qed.

Lemma proof_of_get_positive_entail_wit_1 : get_positive_entail_wit_1.
Proof.
  unfold get_positive_entail_wit_1.
  left. intros. Intros. Exists (@nil Z). entailer!.
  rewrite IntArray.seg_empty.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg retval_2 l_size_pre).
  cancel. entailer!.
Qed.

Lemma proof_of_get_positive_entail_wit_2_1 : get_positive_entail_wit_2_1.
Proof.
  unfold get_positive_entail_wit_2_1.
  left. intros. Intros.
  Exists (output_2 ++ [Znth i input 0]). entailer!.
  - unfold problem_30_prefix_z in *.
    subst output_2.
    rewrite firstn_Z_succ_30 by lia.
    rewrite filter_positive_30_app. simpl.
    assert (Hpos : Z.ltb 0 (Znth i input 0) = true).
    { apply Z.ltb_lt. lia. }
    rewrite Hpos. reflexivity.
  - rewrite Zlength_app, PreH11, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_get_positive_entail_wit_2_2 : get_positive_entail_wit_2_2.
Proof.
  unfold get_positive_entail_wit_2_2.
  left. intros. Intros. Exists output_2. entailer!.
  unfold problem_30_prefix_z in *.
  subst output_2.
  rewrite firstn_Z_succ_30 by lia.
  rewrite filter_positive_30_app. simpl.
  assert (Hnonpos : Z.ltb 0 (Znth i input 0) = false).
  { apply Z.ltb_ge. lia. }
  rewrite Hnonpos. symmetry. apply app_nil_r.
Qed.

Lemma proof_of_get_positive_return_wit_1 : get_positive_return_wit_1.
Proof.
  unfold get_positive_return_wit_1.
  intros. Right. Intros.
  Exists output_2 output_size data_2. entailer!.
  unfold problem_30_spec_z, problem_30_prefix_z in *.
  assert (Hi : i = l_size_pre) by lia. subst i.
  assert (Hlen : Z.to_nat l_size_pre = List.length input).
  { apply Nat2Z.inj. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  rewrite Hlen, firstn_all in PreH12.
  exact PreH12.
Qed.
