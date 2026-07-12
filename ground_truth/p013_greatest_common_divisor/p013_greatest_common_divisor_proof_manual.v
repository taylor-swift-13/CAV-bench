Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p013_greatest_common_divisor Require Import p013_greatest_common_divisor_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p013_greatest_common_divisor.
Local Open Scope sac.

Lemma rem_nonzero_pos : forall x y : Z,
	0 <= x -> 0 < y -> (x % ( y )) <> 0 -> (x % ( y )) > 0.
Proof.
	intros x y Hx_nonneg Hy_pos Hrem_nz.
	rewrite Z.rem_mod_nonneg in Hrem_nz by lia.
	rewrite Z.rem_mod_nonneg by lia.
	pose proof (Z.mod_pos_bound x y Hy_pos) as Hrange.
	lia.
Qed.

Lemma gcd_eq_right_of_mod0 : forall a b : Z,
	0 < b -> a mod b = 0 -> Zgcd a b = b.
Proof.
	intros a b Hb_pos Hmod0.
	assert (Hdiv_b_a : Z.divide b a) by (apply Z.mod_divide; lia).
	assert (Hdiv_b_g : Z.divide b (Zgcd a b)).
	{
		apply Z.gcd_greatest.
		- exact Hdiv_b_a.
		- exists 1. lia.
	}
	assert (Hdiv_g_b : Z.divide (Zgcd a b) b) by apply Z.gcd_divide_r.
	assert (Hg_nonneg : 0 <= Zgcd a b) by apply Z.gcd_nonneg.
	assert (Hg_pos : 0 < Zgcd a b).
	{
		assert (Hg_ne0 : Zgcd a b <> 0).
		{
			intro Hg0.
			destruct Hdiv_g_b as [k Hk].
			rewrite Hg0 in Hk.
			lia.
		}
		lia.
	}
	assert (Hg_le_b : Zgcd a b <= b).
	{
		apply Z.divide_pos_le.
		- exact Hb_pos.
		- exact Hdiv_g_b.
	}
	assert (Hb_le_g : b <= Zgcd a b).
	{
		apply Z.divide_pos_le.
		- exact Hg_pos.
		- exact Hdiv_b_g.
	}
	lia.
Qed.

Lemma proof_of_greatest_common_divisor_entail_wit_2_1 : greatest_common_divisor_entail_wit_2_1.
Proof.
	unfold greatest_common_divisor_entail_wit_2_1.
	right.
	intros.
	Intros.
	entailer!.
	- etransitivity.
		+ apply Z.gcd_rem; lia.
		+ exact PreH3.
	- apply rem_nonzero_pos; lia.
Qed.

Lemma proof_of_greatest_common_divisor_entail_wit_2_2 : greatest_common_divisor_entail_wit_2_2.
Proof.
	unfold greatest_common_divisor_entail_wit_2_2.
	right.
	intros.
	Intros.
	entailer!.
	- etransitivity.
		+ apply Z.gcd_rem; lia.
		+ rewrite Z.gcd_comm; exact PreH3.
	- apply rem_nonzero_pos; lia.
Qed.

Lemma proof_of_greatest_common_divisor_return_wit_1 : greatest_common_divisor_return_wit_1.
Proof.
	unfold greatest_common_divisor_return_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_13_spec.
	assert (Hmod_ba_mod : b mod a = 0).
	{
		rewrite <- Z.rem_mod_nonneg by lia.
		exact PreH1.
	}
	assert (Hg_ba_eq_a : Zgcd b a = a).
	{
		apply gcd_eq_right_of_mod0; lia.
	}
	assert (Hg_ab_eq_a : Zgcd a b = a).
	{
		rewrite Z.gcd_comm.
		exact Hg_ba_eq_a.
	}
	assert (Hg_pre_eq_a : Zgcd a_pre b_pre = a) by lia.
	split.
	- assert (Hdiv : Z.divide a a_pre).
		{
			rewrite <- Hg_pre_eq_a.
			apply Z.gcd_divide_l.
		}
		apply (proj2 (Z.mod_divide a_pre a ltac:(lia))).
		exact Hdiv.
	- split.
		+ assert (Hdiv : Z.divide a b_pre).
			{
				rewrite <- Hg_pre_eq_a.
				apply Z.gcd_divide_r.
			}
			apply (proj2 (Z.mod_divide b_pre a ltac:(lia))).
			exact Hdiv.
		+ intros x Hax Hbx Hx_pos.
			assert (Hx_div_a_pre : Z.divide x a_pre).
			{
				apply (proj1 (Z.mod_divide a_pre x ltac:(lia))).
				exact Hax.
			}
			assert (Hx_div_b_pre : Z.divide x b_pre).
			{
				apply (proj1 (Z.mod_divide b_pre x ltac:(lia))).
				exact Hbx.
			}
			assert (Hx_div_g : Z.divide x (Zgcd a_pre b_pre)).
			{
				apply Z.gcd_greatest; assumption.
			}
			rewrite Hg_pre_eq_a in Hx_div_g.
			apply Z.divide_pos_le.
			* lia.
			* exact Hx_div_g.
Qed.

Lemma proof_of_greatest_common_divisor_return_wit_2 : greatest_common_divisor_return_wit_2.
Proof.
	unfold greatest_common_divisor_return_wit_2.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_13_spec.
	assert (Hmod_ab_mod : a mod b = 0).
	{
		rewrite <- Z.rem_mod_nonneg by lia.
		exact PreH1.
	}
	assert (Hg_ab_eq_b : Zgcd a b = b).
	{
		apply gcd_eq_right_of_mod0; lia.
	}
	assert (Hg_pre_eq_b : Zgcd a_pre b_pre = b) by lia.
	split.
	- assert (Hdiv : Z.divide b a_pre).
		{
			rewrite <- Hg_pre_eq_b.
			apply Z.gcd_divide_l.
		}
		apply (proj2 (Z.mod_divide a_pre b ltac:(lia))).
		exact Hdiv.
	- split.
		+ assert (Hdiv : Z.divide b b_pre).
			{
				rewrite <- Hg_pre_eq_b.
				apply Z.gcd_divide_r.
			}
			apply (proj2 (Z.mod_divide b_pre b ltac:(lia))).
			exact Hdiv.
		+ intros x Hax Hbx Hx_pos.
			assert (Hx_div_a_pre : Z.divide x a_pre).
			{
				apply (proj1 (Z.mod_divide a_pre x ltac:(lia))).
				exact Hax.
			}
			assert (Hx_div_b_pre : Z.divide x b_pre).
			{
				apply (proj1 (Z.mod_divide b_pre x ltac:(lia))).
				exact Hbx.
			}
			assert (Hx_div_g : Z.divide x (Zgcd a_pre b_pre)).
			{
				apply Z.gcd_greatest; assumption.
			}
			rewrite Hg_pre_eq_b in Hx_div_g.
			apply Z.divide_pos_le.
			* lia.
			* exact Hx_div_g.
Qed.
