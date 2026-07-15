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
From SimpleC.EE.CAV.ground_truth_p097_multiply Require Import p097_multiply_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p097_multiply.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  unfold abs_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  unfold abs_return_wit_2.
  left.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_multiply_safety_wit_1 : multiply_safety_wit_1.
Proof.
  unfold multiply_safety_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  - subst retval retval_2.
    set (x := Z.rem (Zabs a_pre) 10).
    set (y := Z.rem (Zabs b_pre) 10).
    assert (Hx: 0 <= x < 10).
    { subst x. apply Z.rem_bound_pos; [apply Z.abs_nonneg | lia]. }
    assert (Hy: 0 <= y < 10).
    { subst y. apply Z.rem_bound_pos; [apply Z.abs_nonneg | lia]. }
    nia.
  - subst retval retval_2.
    set (x := Z.rem (Zabs a_pre) 10).
    set (y := Z.rem (Zabs b_pre) 10).
    assert (Hx: 0 <= x < 10).
    { subst x. apply Z.rem_bound_pos; [apply Z.abs_nonneg | lia]. }
    assert (Hy: 0 <= y < 10).
    { subst y. apply Z.rem_bound_pos; [apply Z.abs_nonneg | lia]. }
    nia.
Qed.

Lemma proof_of_multiply_return_wit_1 : multiply_return_wit_1.
Proof.
  unfold multiply_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  unfold problem_97_spec.
  subst.
  rewrite Z.rem_mod_nonneg by (try apply Z.abs_nonneg; lia).
  rewrite Z.rem_mod_nonneg by (try apply Z.abs_nonneg; lia).
  reflexivity.
Qed.
