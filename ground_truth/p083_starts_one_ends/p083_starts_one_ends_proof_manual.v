Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p083_starts_one_ends Require Import p083_starts_one_ends_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p083_starts_one_ends.
Local Open Scope sac.

Lemma proof_of_starts_one_ends_safety_wit_8 : starts_one_ends_safety_wit_8.
Proof.
  unfold starts_one_ends_safety_wit_8.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hi : i - 2 <= 6) by lia.
  assert (Hi0 : 0 <= i - 2) by lia.
  assert (H10 : 10 ^ (i - 2) <= 10 ^ 6).
  { apply Z.pow_le_mono_r; lia. }
  assert (H10nn : 0 <= 10 ^ (i - 2)).
  { apply Z.pow_nonneg; lia. }
  nia.
Qed.

Lemma proof_of_starts_one_ends_entail_wit_2 : starts_one_ends_entail_wit_2.
Proof.
  unfold starts_one_ends_entail_wit_2.
  left.
  intros.
  Intros.
  entailer!.
  subst out.
  replace ((i + 1) - 2) with ((i - 2) + 1) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma proof_of_starts_one_ends_return_wit_1 : starts_one_ends_return_wit_1.
Proof.
  unfold starts_one_ends_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hieq : i = n_pre) by lia.
  subst i.
  unfold problem_83_spec_z, problem_83_spec.
  intros _.
  right.
  split.
  - assert (Hn : n_pre >= 2) by lia.
    lia.
  - subst out.
    rewrite Z2Nat.inj_mul by (try lia; apply Z.pow_nonneg; lia).
    simpl (Z.to_nat 18).
    f_equal.
    rewrite Z2Nat.inj_pow by lia.
    rewrite Z2Nat.inj_sub by lia.
    simpl (Z.to_nat 10). simpl (Z.to_nat 2).
    reflexivity.
Qed.

Lemma proof_of_starts_one_ends_return_wit_2 : starts_one_ends_return_wit_2.
Proof.
  unfold starts_one_ends_return_wit_2.
  left.
  intros.
  Intros.
  entailer!.
  unfold problem_83_spec_z, problem_83_spec.
  subst.
  simpl.
  intros _.
  left.
  split; reflexivity.
Qed.
