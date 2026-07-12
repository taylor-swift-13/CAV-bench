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
