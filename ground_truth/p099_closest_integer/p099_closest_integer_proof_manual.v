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
From SimpleC.EE.CAV.ground_truth_p099_closest_integer Require Import p099_closest_integer_goal.
From SimpleC.EE.CAV.ground_truth_p099_closest_integer Require Import p099_closest_integer_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p099_closest_integer.
Local Open Scope sac.

Ltac solve_ratio_safety :=
  intros; Intros;
  unfold problem_99_pre_ratio in *;
  entailer!; lia.

Ltac solve_ratio_return :=
  intros; Intros; entailer!;
  unfold problem_99_spec_ratio, round_away_99;
  cbn;
  repeat match goal with
  | |- context[Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
  | |- context[Z.leb ?a ?b] => destruct (Z.leb_spec a b)
  end; lia.

Lemma proof_of_closest_integer_safety_wit_1 : closest_integer_safety_wit_1.
Proof. unfold closest_integer_safety_wit_1; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_safety_wit_2 : closest_integer_safety_wit_2.
Proof. unfold closest_integer_safety_wit_2; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_safety_wit_4 : closest_integer_safety_wit_4.
Proof. unfold closest_integer_safety_wit_4; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_safety_wit_6 : closest_integer_safety_wit_6.
Proof. unfold closest_integer_safety_wit_6; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_safety_wit_9 : closest_integer_safety_wit_9.
Proof. unfold closest_integer_safety_wit_9; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_safety_wit_12 : closest_integer_safety_wit_12.
Proof. unfold closest_integer_safety_wit_12; left; solve_ratio_safety. Qed.

Lemma proof_of_closest_integer_return_wit_1 : closest_integer_return_wit_1.
Proof.
  unfold closest_integer_return_wit_1; left. intros. Intros. entailer!.
  unfold problem_99_spec_ratio, round_away_99. cbv zeta.
  assert (Hr : Z.rem numerator_pre denominator_pre = 0) by lia.
  rewrite Hr. reflexivity.
Qed.

Lemma proof_of_closest_integer_return_wit_2 : closest_integer_return_wit_2.
Proof.
  unfold closest_integer_return_wit_2; left. intros. Intros. entailer!.
  unfold problem_99_spec_ratio, round_away_99. cbv zeta.
  assert (Hp : (0 <? Z.rem numerator_pre denominator_pre) = false)
    by (apply Z.ltb_ge; lia).
  assert (Hn : (Z.rem numerator_pre denominator_pre <? 0) = true)
    by (apply Z.ltb_lt; lia).
  rewrite Hp, Hn.
  destruct (denominator_pre <=?
      (-2) * Z.rem numerator_pre denominator_pre) eqn:E.
  - apply Z.leb_le in E. exfalso. lia.
  - reflexivity.
Qed.

Lemma proof_of_closest_integer_return_wit_3 : closest_integer_return_wit_3.
Proof.
  unfold closest_integer_return_wit_3; left. intros. Intros. entailer!.
  unfold problem_99_spec_ratio, round_away_99. cbv zeta.
  assert (Hp : (0 <? Z.rem numerator_pre denominator_pre) = false)
    by (apply Z.ltb_ge; lia).
  assert (Hn : (Z.rem numerator_pre denominator_pre <? 0) = true)
    by (apply Z.ltb_lt; lia).
  rewrite Hp, Hn.
  destruct (denominator_pre <=?
      (-2) * Z.rem numerator_pre denominator_pre) eqn:E.
  - reflexivity.
  - apply Z.leb_gt in E. exfalso. lia.
Qed.

Lemma proof_of_closest_integer_return_wit_4 : closest_integer_return_wit_4.
Proof.
  unfold closest_integer_return_wit_4; left. intros. Intros. entailer!.
  unfold problem_99_spec_ratio, round_away_99. cbv zeta.
  assert (Hp : (0 <? Z.rem numerator_pre denominator_pre) = true)
    by (apply Z.ltb_lt; lia).
  assert (Ht : (denominator_pre <=? 2 * Z.rem numerator_pre denominator_pre) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hp, Ht. reflexivity.
Qed.

Lemma proof_of_closest_integer_return_wit_5 : closest_integer_return_wit_5.
Proof.
  unfold closest_integer_return_wit_5; left. intros. Intros. entailer!.
  unfold problem_99_spec_ratio, round_away_99. cbv zeta.
  assert (Hp : (0 <? Z.rem numerator_pre denominator_pre) = true)
    by (apply Z.ltb_lt; lia).
  assert (Ht : (denominator_pre <=? 2 * Z.rem numerator_pre denominator_pre) = true)
    by (apply Z.leb_le; lia).
  rewrite Hp, Ht. reflexivity.
Qed.
