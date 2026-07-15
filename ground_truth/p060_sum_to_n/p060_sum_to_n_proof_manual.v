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
From SimpleC.EE.CAV.ground_truth_p060_sum_to_n Require Import p060_sum_to_n_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p060_sum_to_n.
Local Open Scope sac.

Lemma proof_of_sum_to_n_return_wit_1 : sum_to_n_return_wit_1.
Proof.
	unfold sum_to_n_return_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_60_spec_z, problem_60_spec.
	set (prod := n_pre * (n_pre + 1)).
	assert (Hn_nonneg : (0 <= n_pre)%Z).
	{ apply Z.le_trans with (m := 1); [now compute | exact PreH2]. }
	assert (Hnp1_nonneg : (0 <= n_pre + 1)%Z).
	{ apply Z.add_nonneg_nonneg; [exact Hn_nonneg | now compute]. }
	assert (Hprod_nonneg : (0 <= prod)%Z).
	{ unfold prod. apply Z.mul_nonneg_nonneg; assumption. }
	replace (Z.to_nat n_pre * (Z.to_nat n_pre + 1))%nat with (Z.to_nat prod).
	2: {
		unfold prod.
		replace (Z.to_nat n_pre + 1)%nat with (Z.to_nat (n_pre + 1)).
		2: {
			rewrite (Z2Nat.inj_add n_pre 1); [reflexivity | exact Hn_nonneg | now compute].
		}
		rewrite <- (Z2Nat.inj_mul n_pre (n_pre + 1)); [reflexivity | exact Hn_nonneg | exact Hnp1_nonneg].
	}
	assert (Hmod : (prod mod 2 = 0)%Z).
	{
		rewrite Zmod_even.
		assert (Heven : Z.even prod = true).
		{
			unfold prod.
			rewrite Z.even_mul.
			rewrite Z.even_add.
			rewrite Z.even_1.
			destruct (Z.even n_pre); reflexivity.
		}
		rewrite Heven. reflexivity.
	}
	assert (Hdivides : (2 | prod)).
	{ apply Z.mod_divide; [discriminate | exact Hmod]. }
	assert (Hquot : (prod ÷ 2 = prod / 2)%Z).
	{ apply Z.quot_div_exact; [discriminate | exact Hdivides]. }
	rewrite Hquot.
	assert (Hdiv_nonneg : (0 <= prod / 2)%Z).
	{ apply Z.div_pos; [exact Hprod_nonneg | now compute]. }
	assert (Hdiv_eq : (prod = 2 * (prod / 2))%Z).
	{ apply Z_div_exact_2; [now compute | exact Hmod]. }
	replace 2%nat with (Z.to_nat 2) by reflexivity.
	rewrite <- (Z2Nat.inj_mul 2 (prod / 2)).
	2: { now compute. }
	2: { exact Hdiv_nonneg. }
	pose proof (f_equal Z.to_nat Hdiv_eq) as Hnat_eq.
	exact (eq_sym Hnat_eq).
Qed.
