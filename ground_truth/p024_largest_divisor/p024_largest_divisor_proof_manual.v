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
From SimpleC.EE.CAV.ground_truth_p024_largest_divisor Require Import p024_largest_divisor_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p024_largest_divisor.
Local Open Scope sac.

Lemma proof_of_largest_divisor_safety_wit_2 : largest_divisor_safety_wit_2.
Proof.
	unfold largest_divisor_safety_wit_2.
	left; intros.
	apply _derivable1_andp_intros; apply dump_spatial_left; nia.
Qed.

Lemma proof_of_largest_divisor_entail_wit_2 : largest_divisor_entail_wit_2.
Proof.
	unfold largest_divisor_entail_wit_2.
	left.
	intros.
	Intros.
	entailer!.
	-	intros k Hk.
		destruct Hk as [Hk_ge2 Hk_lt_i1].
		assert (k < i \/ k = i) as Hcase by lia.
		destruct Hcase as [Hk_lt_i | Hk_eq_i].
		+	apply PreH5; lia.
		+	subst k.
			exact PreH1.
	-	assert (Hi_lt : i < 46340).
		{
			destruct (Z.eq_dec i 46340) as [Hi_eq | Hi_neq].
			+	subst i.
				assert (Hn_eq : n_pre = 2147395600) by nia.
				subst n_pre.
				vm_compute in PreH1.
				contradiction.
			+	lia.
		}
		lia.
Qed.

Lemma proof_of_largest_divisor_return_wit_1 : largest_divisor_return_wit_1.
Proof.
	unfold largest_divisor_return_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_24_spec_z, problem_24_spec.
	split.
	-	apply Nat.mod_1_r.
	-	split.
		+	replace 1%nat with (Z.to_nat 1) by reflexivity.
			assert (Hone_nonneg : 0 <= 1) by lia.
			assert (Hn_nonneg : 0 <= n_pre) by lia.
			apply (proj1 (Z2Nat.inj_lt 1 n_pre Hone_nonneg Hn_nonneg)).
			lia.
		+	intros j Hj_range Hj_div.
			destruct Hj_range as [Hj_pos Hj_lt_n].
			destruct (le_lt_dec j 1) as [Hj_le_1 | Hj_gt_1].
			*	exact Hj_le_1.
			*	exfalso.
			assert (Hj_ge_2 : 2 <= Z.of_nat j) by lia.
			assert (Hj_divides : exists c : nat, Z.to_nat n_pre = (j * c)%nat).
			{
				apply Nat.Div0.mod_divides in Hj_div.
				exact Hj_div.
			}
			destruct Hj_divides as [c Hnat_eq].
			assert (Hc_ge_2 : (2 <= c)%nat).
			{
				destruct c.
				-	simpl in Hnat_eq; lia.
				-	destruct c.
					+	simpl in Hnat_eq; lia.
					+	lia.
			}
			assert (Hzj_pos : 0 < Z.of_nat j) by lia.
			assert (Hzc_ge_2 : 2 <= Z.of_nat c) by lia.
			assert (Hn_eq_factor : n_pre = Z.of_nat j * Z.of_nat c).
			{
				pose proof (f_equal Z.of_nat Hnat_eq) as Hz_eq.
				rewrite Nat2Z.inj_mul in Hz_eq.
				rewrite Z2Nat.id in Hz_eq by lia.
				exact Hz_eq.
			}
			destruct (Z_lt_ge_dec (Z.of_nat j) i) as [Hj_lt_i | Hj_ge_i].
			{
				match goal with
				| Hinv : forall k : Z, ((2 <= k /\ k < i) -> ((n_pre % ( k ) ) <> 0)) |- _ =>
					assert (Hj_range_z : (2 <= Z.of_nat j /\ Z.of_nat j < i)) by lia;
					specialize (Hinv (Z.of_nat j) Hj_range_z);
					apply Hinv
				end.
				rewrite Hn_eq_factor.
				assert (Hzj_nz : Z.of_nat j <> 0) by lia.
				apply (proj2 (Z.rem_divide (Z.of_nat j * Z.of_nat c) (Z.of_nat j) Hzj_nz)).
				exists (Z.of_nat c).
				rewrite Z.mul_comm.
				reflexivity.
			}
			{
				assert (Hc_lt_i : Z.of_nat c < i) by nia.
				match goal with
				| Hinv : forall k : Z, ((2 <= k /\ k < i) -> ((n_pre % ( k ) ) <> 0)) |- _ =>
					assert (Hc_range : (2 <= Z.of_nat c /\ Z.of_nat c < i)) by lia;
					specialize (Hinv (Z.of_nat c) Hc_range);
					apply Hinv
				end.
				rewrite Hn_eq_factor.
				assert (Hzc_nz : Z.of_nat c <> 0) by lia.
				apply (proj2 (Z.rem_divide (Z.of_nat j * Z.of_nat c) (Z.of_nat c) Hzc_nz)).
				exists (Z.of_nat j).
				rewrite Z.mul_comm.
				reflexivity.
			}
Qed.

Lemma proof_of_largest_divisor_return_wit_2 : largest_divisor_return_wit_2.
Proof.
	unfold largest_divisor_return_wit_2.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_24_spec_z, problem_24_spec.
	assert (Hn_nonneg : 0 <= n_pre) by lia.
	assert (Hi_pos : 0 < i) by lia.
	assert (Hi_nonzero : i <> 0) by lia.
	assert (Hquot_eq : n_pre = i * (n_pre ÷ i)).
	{
		apply (proj2 (Z.quot_exact n_pre i Hi_nonzero)).
		exact PreH1.
	}
	assert (Hq_nonneg : 0 <= n_pre ÷ i).
	{
		apply Z.quot_pos; lia.
	}
	split.
	-	assert (Hnat_mul : Z.to_nat n_pre = (Z.to_nat i * Z.to_nat (n_pre ÷ i))%nat).
		{
			pose proof (f_equal Z.to_nat Hquot_eq) as Htmp.
			rewrite Z2Nat.inj_mul in Htmp by lia.
			exact Htmp.
		}
		rewrite Hnat_mul.
		apply Nat.Div0.mod_mul.
	-	split.
		+	replace (Z.to_nat (n_pre ÷ i)) with (Z.to_nat (n_pre ÷ i)).
			2: reflexivity.
			apply (proj1 (Z2Nat.inj_lt (n_pre ÷ i) n_pre Hq_nonneg Hn_nonneg)).
			apply Z.quot_lt; lia.
		+	intros j Hj_range Hj_div.
			destruct Hj_range as [Hj_pos Hj_lt_n].
			assert (Hj_divides : exists c : nat, Z.to_nat n_pre = (j * c)%nat).
			{
				apply Nat.Div0.mod_divides in Hj_div.
				exact Hj_div.
			}
			destruct Hj_divides as [c Hnat_eq].
			assert (Hc_ge_2 : (2 <= c)%nat).
			{
				destruct c.
				-	simpl in Hnat_eq; lia.
				-	destruct c.
					+	simpl in Hnat_eq; lia.
					+	lia.
			}
			assert (Hzc_ge_2 : 2 <= Z.of_nat c) by lia.
			assert (Hn_eq_factor : n_pre = Z.of_nat j * Z.of_nat c).
			{
				pose proof (f_equal Z.of_nat Hnat_eq) as Hz_eq.
				rewrite Nat2Z.inj_mul in Hz_eq.
				rewrite Z2Nat.id in Hz_eq by lia.
				exact Hz_eq.
			}
			assert (Hi_le_c : i <= Z.of_nat c).
			{
				destruct (Z_lt_ge_dec (Z.of_nat c) i) as [Hc_lt_i | Hc_ge_i].
				+	exfalso.
					specialize (PreH5 (Z.of_nat c)).
					assert (Hc_range : (2 <= Z.of_nat c /\ Z.of_nat c < i)) by lia.
					specialize (PreH5 Hc_range).
					apply PreH5.
					rewrite Hn_eq_factor.
					assert (Hzc_nz : Z.of_nat c <> 0) by lia.
					apply (proj2 (Z.rem_divide (Z.of_nat j * Z.of_nat c) (Z.of_nat c) Hzc_nz)).
					exists (Z.of_nat j).
					rewrite Z.mul_comm.
					reflexivity.
				+	lia.
			}
			assert (Hzj_le_q : Z.of_nat j <= n_pre ÷ i).
			{
				apply Z.quot_le_lower_bound; try lia.
				rewrite Z.mul_comm.
				rewrite Hn_eq_factor.
				apply Z.mul_le_mono_nonneg_l; lia.
			}
			replace j with (Z.to_nat (Z.of_nat j)) by apply Nat2Z.id.
			apply (proj1 (Z2Nat.inj_le (Z.of_nat j) (n_pre ÷ i) (Nat2Z.is_nonneg j) Hq_nonneg)).
			exact Hzj_le_q.
Qed.
