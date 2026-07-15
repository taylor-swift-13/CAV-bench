Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
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
From SimpleC.EE.CAV.ground_truth_p075_is_multiply_prime Require Import p075_is_multiply_prime_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p075_is_multiply_prime.
Local Open Scope sac.

Lemma list_prod_app_single :
	forall (l : list Z) (x : Z),
		list_prod (l ++ (x :: nil)) = list_prod l * x.
Proof.
	intros l x.
	induction l.
	- simpl. rewrite Z.mul_1_r. destruct x; reflexivity.
	- simpl. rewrite IHl. rewrite Z.mul_assoc. reflexivity.
Qed.

Lemma mp_outer_inv_inc_no_div :
	forall a_pre i a num,
		Z.rem a i <> 0 ->
		mp_outer_inv a_pre i a num ->
		mp_outer_inv a_pre (i + 1) a num.
Proof.
	intros a_pre i a num Hmod_i Hinv.
	unfold mp_outer_inv in *.
	destruct Hinv as [Ha [l [Hlprime [Hlen [Heq Hnodiv]]]]].
	split.
	{ exact Ha. }
	{
	  exists l.
	  repeat split; try assumption.
	  intros k Hk.
	  assert (k < i \/ k = i) by lia.
	  destruct H as [Hlt | Heqk].
	  - apply Hnodiv; lia.
	  - subst k. left. exact Hmod_i.
	}
Qed.

Lemma mp_outer_inv_inc_le :
	forall a_pre i a num,
		a <= i ->
		mp_outer_inv a_pre i a num ->
		mp_outer_inv a_pre (i + 1) a num.
Proof.
	intros a_pre i a num Hale Hinv.
	unfold mp_outer_inv in *.
	destruct Hinv as [Ha [l [Hlprime [Hlen [Heq Hnodiv]]]]].
	split.
	{ exact Ha. }
	{
	  exists l.
	  repeat split; try assumption.
	  intros k Hk.
	  assert (k < i \/ k = i) by lia.
	  destruct H as [Hlt | Heqk].
	  - apply Hnodiv; lia.
	  - subst k. right. lia.
	}
Qed.

Lemma current_divisor_is_prime :
	forall a i,
		a > i ->
		Z.rem a i = 0 ->
		2 <= i ->
		(forall k, 2 <= k < i -> Z.rem a k <> 0 \/ a <= k) ->
		prime i.
Proof.
	intros a i Hgt Hmod Hi Hnodiv.
	destruct (prime_dec i) as [Hp | Hnp].
	- exact Hp.
	- exfalso.
	assert (Hione : 1 < i) by lia.
	destruct (not_prime_divide i Hione Hnp) as [d [[Hd1 Hd2] Hdiv_di]].
	assert (Hd_range : 2 <= d < i) by lia.
	specialize (Hnodiv d Hd_range).
	assert (Ha_gt_d : a > d) by lia.
	assert (Hdiv_ia : (i | a)).
	{
		apply Z.rem_divide.
		- lia.
		- exact Hmod.
	}
	assert (Hdiv_da : (d | a)).
	{
		eapply Z.divide_trans; eauto.
	}
	destruct Hnodiv as [Hmod_d | Ha_le_d].
	+ assert (Ha_mod_d_zero : Z.rem a d = 0).
	  {
		  apply Z.rem_divide.
		  - lia.
		  - exact Hdiv_da.
	  }
	  contradiction.
	+ lia.
Qed.

Lemma mp_outer_inv_div_step :
	forall a_pre i a num,
		a > i ->
		Z.rem a i = 0 ->
		2 <= i ->
		mp_outer_inv a_pre i a num ->
		mp_outer_inv a_pre i (a ÷ i) (num + 1).
Proof.
	intros a_pre i a num Hgt Hmod Hi Hinv.
	unfold mp_outer_inv in *.
	destruct Hinv as [Ha [l [Hlprime [Hlen [Heq Hnodiv]]]]].
	assert (Hi_pos : 0 < i) by lia.
	assert (Hprime_i : prime i).
	{
		apply (current_divisor_is_prime a i); auto.
	}
	assert (Hdiv_ia : (i | a)).
	{
		apply Z.rem_divide.
		- lia.
		- exact Hmod.
	}
	destruct Hdiv_ia as [q Hq].
	assert (Hqeq : q = a ÷ i).
	{
		apply Z.quot_unique_exact.
		- lia.
		- rewrite Z.mul_comm.
		  exact Hq.
	}
	assert (Ha_q : a = i * (a ÷ i)).
	{
		rewrite <- Hqeq.
		rewrite Z.mul_comm.
		exact Hq.
	}
	split.
	- nia.
	- exists (l ++ (i :: nil)).
		repeat split.
		+ apply Forall_app.
		  split.
		  * exact Hlprime.
		  * constructor.
			{ exact Hprime_i. }
			{ constructor. }
		+ rewrite app_length. simpl.
		  rewrite Nat2Z.inj_add. simpl. lia.
		+ rewrite list_prod_app_single.
		  rewrite Ha_q in Heq.
		  lia.
		+ intros k Hk.
		  left.
		  intro Hmod_qk.
		  assert (Hdiv_qk : (k | (a ÷ i))).
		  {
			apply Z.rem_divide.
			- lia.
			- exact Hmod_qk.
		  }
		  destruct Hdiv_qk as [t Ht].
		  assert (Hdiv_ka : (k | a)).
		  {
			exists (i * t).
			rewrite Ha_q, Ht.
			lia.
		  }
		  assert (Hmod_ak : Z.rem a k = 0).
		  {
			apply Z.rem_divide.
			- lia.
			- exact Hdiv_ka.
		  }
		  specialize (Hnodiv k Hk).
		  assert (Ha_gt_k : a > k) by lia.
		  destruct Hnodiv as [Hmod_ak_ne | Ha_le_k].
		  * contradiction.
		  * lia.
Qed.

Lemma three_primes_ge_8 :
	forall p1 p2 p3 : Z,
		prime p1 -> prime p2 -> prime p3 ->
		8 <= p1 * p2 * p3.
Proof.
	intros p1 p2 p3 Hp1 Hp2 Hp3.
	pose proof (prime_ge_2 _ Hp1).
	pose proof (prime_ge_2 _ Hp2).
	pose proof (prime_ge_2 _ Hp3).
	nia.
Qed.

Lemma list_prod_forall_prime_ge_1 :
	forall l : list Z,
		Forall prime l -> 1 <= list_prod l.
Proof.
	intros l Hl.
	induction Hl.
	- simpl. lia.
	- simpl.
		pose proof (prime_ge_2 _ H).
		nia.
Qed.

Lemma list_prod_forall_prime_nonempty_ge_2 :
	forall l : list Z,
		Forall prime l ->
		l <> nil ->
		2 <= list_prod l.
Proof.
	intros l Hl Hne.
	destruct Hl.
	- contradiction.
	- simpl.
		pose proof (prime_ge_2 _ H).
		pose proof (list_prod_forall_prime_ge_1 l Hl).
		nia.
Qed.

Lemma list_prod_eq_prime_len1 :
	forall l p,
		Forall prime l ->
		prime p ->
		list_prod l = p ->
		Z.of_nat (length l) = 1.
Proof.
	intros l p Hl Hp Heq.
	induction Hl.
	- simpl in Heq.
		pose proof (prime_ge_2 _ Hp).
		lia.
	- simpl in Heq.
		assert (Hx_div_p : (x | p)).
		{
			exists (list_prod l).
			nia.
		}
		assert (Hx_eq_p : x = p).
		{
			eapply prime_div_prime; eauto.
		}
		subst x.
		assert (Hp_nz : p <> 0).
		{
			pose proof (prime_ge_2 _ Hp).
			lia.
		}
		assert (Hprod1 : list_prod l = 1).
		{
			apply (Z.mul_reg_l (list_prod l) 1 p); try exact Hp_nz.
			lia.
		}
		destruct l.
		+ simpl. lia.
		+ exfalso.
			assert (Hys_ge2 : 2 <= list_prod (z :: l)).
			{
				apply list_prod_forall_prime_nonempty_ge_2.
				* exact Hl.
				* discriminate.
			}
			simpl in Hprod1.
			nia.
Qed.

Lemma list_prod_eq_two_primes_len2 :
	forall l p q,
		Forall prime l ->
		prime p ->
		prime q ->
		list_prod l = p * q ->
		Z.of_nat (length l) = 2.
Proof.
	intros l p q Hl Hp Hq Heq.
	induction Hl.
	- simpl in Heq.
		pose proof (prime_ge_2 _ Hp).
		pose proof (prime_ge_2 _ Hq).
		nia.
	- simpl in Heq.
		assert (Hx_div_pq : (x | p * q)).
		{
			exists (list_prod l).
			nia.
		}
		pose proof (prime_mult x H p q Hx_div_pq) as [Hx_div_p | Hx_div_q].
		+ assert (Hx_eq_p : x = p).
			{
				eapply prime_div_prime; eauto.
			}
			subst x.
			assert (Hp_nz : p <> 0).
			{
				pose proof (prime_ge_2 _ Hp).
				lia.
			}
			assert (Hxs_eq_q : list_prod l = q).
			{
				apply (Z.mul_reg_l (list_prod l) q p); try exact Hp_nz.
				lia.
			}
			assert (Hlen_xs : Z.of_nat (length l) = 1).
			{
				exact (list_prod_eq_prime_len1 l q Hl Hq Hxs_eq_q).
			}
			simpl.
			lia.
		+ assert (Hx_eq_q : x = q).
			{
				eapply prime_div_prime; eauto.
			}
			subst x.
			assert (Hq_nz : q <> 0).
			{
				pose proof (prime_ge_2 _ Hq).
				lia.
			}
			assert (Hxs_eq_p : list_prod l = p).
			{
				apply (Z.mul_reg_l (list_prod l) p q); try exact Hq_nz.
				nia.
			}
			assert (Hlen_xs : Z.of_nat (length l) = 1).
			{
				exact (list_prod_eq_prime_len1 l p Hl Hp Hxs_eq_p).
			}
			simpl.
			lia.
Qed.

Lemma composite_has_small_prime_divisor :
	forall n : Z,
	2 <= n ->
	~ prime n ->
	exists p : Z, prime p /\ Z.divide p n /\ p * p <= n.
Proof.
	refine (well_founded_induction_type (Z.lt_wf 1)
		(fun n => 2 <= n -> ~ prime n -> exists p, prime p /\ Z.divide p n /\ p * p <= n) _).
	intros n IH Hn2 Hn_not_prime.
	assert (Hn_gt1 : 1 < n) by lia.
	destruct (not_prime_divide n Hn_gt1 Hn_not_prime) as [d [[Hd_gt1 Hd_lt_n] Hd_div_n]].
	destruct Hd_div_n as [k Hn_eq].
	set (m := Z.min d k).
	assert (Hm_lt_n : m < n).
	{
		unfold m.
		destruct (Z_le_gt_dec d k) as [Hdk | Hdk].
		- rewrite Z.min_l by lia; nia.
		- rewrite Z.min_r by lia; nia.
	}
	assert (Hm_gt1 : 1 < m).
	{
		unfold m.
		destruct (Z_le_gt_dec d k) as [Hdk | Hdk].
		- rewrite Z.min_l by lia; nia.
		- rewrite Z.min_r by lia; nia.
	}
	assert (Hm_div_n : Z.divide m n).
	{
		unfold m.
		destruct (Z_le_gt_dec d k) as [Hdk | Hdk].
		- rewrite Z.min_l by lia. exists k. exact Hn_eq.
		- rewrite Z.min_r by lia. exists d. subst n. ring.
	}
	destruct (prime_dec m) as [Hm_prime | Hm_not_prime].
	- exists m.
		split.
		+ exact Hm_prime.
		+ split.
		  * exact Hm_div_n.
		  * unfold m.
			destruct (Z_le_gt_dec d k) as [Hdk | Hdk].
			{ rewrite Z.min_l by lia. subst n. nia. }
			{ rewrite Z.min_r by lia. subst n. nia. }
	- specialize (IH m).
		assert (Hm_range : 1 <= m < n) by lia.
		specialize (IH Hm_range).
		assert (Hm_ge2 : 2 <= m) by lia.
		specialize (IH Hm_ge2 Hm_not_prime).
		destruct IH as [p [Hp_prime [Hp_div_m Hp_sq_le_m]]].
		exists p.
		split.
		+ exact Hp_prime.
		+ split.
		  * eapply Z.divide_trans; eauto.
		  * lia.
Qed.

Lemma prime_from_mp_outer_inv_exit :
	forall a i,
		a >= 2 ->
		i >= 2 ->
		i * i > a ->
		(forall k : Z, 2 <= k < i -> Z.rem a k <> 0 \/ a <= k) ->
		prime a.
Proof.
	intros a i Ha2 Hi2 Hexit Hnodiv.
	destruct (prime_dec a) as [Ha_prime | Ha_not_prime].
	- exact Ha_prime.
	- exfalso.
		assert (Ha2' : 2 <= a) by lia.
		destruct (composite_has_small_prime_divisor a Ha2' Ha_not_prime)
			as [p [Hp_prime [Hp_div_a Hp_sq_le_a]]].
		assert (Hp_ge2 : 2 <= p).
		{
			apply prime_ge_2.
			exact Hp_prime.
		}
		assert (Hp_lt_i : p < i).
		{
			apply Z.nle_gt.
			intro Hp_ge_i.
			assert (Hi_sq_le_p_sq : i * i <= p * p) by nia.
			lia.
		}
		specialize (Hnodiv p).
		assert (Hsplit : Z.rem a p <> 0 \/ a <= p).
		{
			apply Hnodiv.
			split; lia.
		}
		destruct Hsplit as [Hrem_ne | Ha_le_p].
		+ assert (Hrem0 : Z.rem a p = 0).
			{
				apply Z.rem_divide.
				- lia.
				- exact Hp_div_a.
			}
			contradiction.
		+ assert (Hp_lt_a : p < a) by nia.
			lia.
Qed.

Lemma proof_of_is_multiply_prime_entail_wit_1 : is_multiply_prime_entail_wit_1.
Proof.
	unfold is_multiply_prime_entail_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold mp_outer_inv.
	split.
	- lia.
	- exists (@nil Z).
	  split.
	  + constructor.
	  + split.
	    * reflexivity.
	    * split.
	      { cbn [list_prod]. lia. }
	      { intros k Hk. lia. }
Qed.

Lemma proof_of_is_multiply_prime_entail_wit_3_1 : is_multiply_prime_entail_wit_3_1.
Proof.
	unfold is_multiply_prime_entail_wit_3_1.
	left.
	intros.
	Intros.
	entailer!.
	all: try lia.
	eapply mp_outer_inv_inc_no_div; eauto.
Qed.

Lemma proof_of_is_multiply_prime_entail_wit_3_2 : is_multiply_prime_entail_wit_3_2.
Proof.
	unfold is_multiply_prime_entail_wit_3_2.
	left.
	intros.
	Intros.
	entailer!.
	all: try lia.
	eapply mp_outer_inv_inc_le; eauto.
Qed.

Lemma proof_of_is_multiply_prime_entail_wit_4 : is_multiply_prime_entail_wit_4.
Proof.
	unfold is_multiply_prime_entail_wit_4.
	left.
	intros.
	Intros.
	entailer!.
	- assert (Hi2 : 2 <= i_2) by lia.
	  exact (mp_outer_inv_div_step a_pre i_2 a_2 num_2 PreH1 PreH2 Hi2 PreH9).
	- assert (Hq_le_a2m1 : a_2 ÷ i_2 <= a_2 - 1).
	  {
		apply Z.quot_le_upper_bound; nia.
	  }
	  nia.
	- assert (Hq_le_a2m1 : a_2 ÷ i_2 <= a_2 - 1).
	  {
		apply Z.quot_le_upper_bound; nia.
	  }
	  eapply Z.le_trans.
	  + exact Hq_le_a2m1.
	  + lia.
	- assert (Hdiv_i_a2 : (i_2 | a_2)).
	  {
		apply Z.rem_divide.
		- lia.
		- exact PreH2.
	  }
	  destruct Hdiv_i_a2 as [q Hq].
	  assert (Hq_eq : q = a_2 ÷ i_2).
	  {
		apply Z.quot_unique_exact.
		- lia.
		- rewrite Z.mul_comm.
		  exact Hq.
	  }
	  assert (Hq_ge2 : 2 <= q).
	  {
		rewrite Hq in PreH1.
		nia.
	  }
	  rewrite <- Hq_eq.
	  lia.
Qed.

Lemma proof_of_is_multiply_prime_return_wit_1 : is_multiply_prime_return_wit_1.
Proof.
	unfold is_multiply_prime_return_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_75_spec_z.
	split.
	- intro Hfalse.
	  contradiction.
	- intros (p1 & p2 & p3 & Hp1 & Hp2 & Hp3 & Hprod3).
		match goal with
		| Hinv : mp_outer_inv _ _ _ _ |- _ =>
			destruct Hinv as [Ha_ge2 [l [Hlprime [Hlen [Heq Hnodiv]]]]]
		end.
		assert (Hprime_a : prime a).
		{
			apply (prime_from_mp_outer_inv_exit a i).
			- exact Ha_ge2.
			- lia.
			- lia.
			- exact Hnodiv.
		}
		assert (Hdiv_a : (a | p1 * p2 * p3)).
		{
			exists (list_prod l).
			rewrite <- Hprod3.
			rewrite Heq.
			ring.
		}
		assert (Ha_eq_one : a = p1 \/ a = p2 \/ a = p3).
		{
			assert (Hdiv_a_1 : (a | p1 * (p2 * p3))).
			{
				replace (p1 * (p2 * p3)) with (p1 * p2 * p3) by ring.
				exact Hdiv_a.
			}
			pose proof (prime_mult a Hprime_a p1 (p2 * p3) Hdiv_a_1) as [Ha_div_p1 | Ha_div_p23].
			- left.
			  eapply prime_div_prime; eauto.
			- pose proof (prime_mult a Hprime_a p2 p3 Ha_div_p23) as [Ha_div_p2 | Ha_div_p3].
			  + right. left. eapply prime_div_prime; eauto.
			  + right. right. eapply prime_div_prime; eauto.
		}
		assert (Hlen_is_2 : Z.of_nat (length l) = 2).
		{
			destruct Ha_eq_one as [Ha_p1 | [Ha_p2 | Ha_p3]].
			- subst a.
			  assert (Hprod_l : list_prod l = p2 * p3).
			  {
				assert (Htmp : list_prod l * p1 = (p2 * p3) * p1).
				{
					rewrite <- Heq.
					rewrite Hprod3.
					ring.
				}
				assert (Hp1_nz : p1 <> 0).
				{
					pose proof (prime_ge_2 _ Hp1).
					lia.
				}
				apply (Z.mul_reg_r (list_prod l) (p2 * p3) p1); auto.
			  }
			  exact (list_prod_eq_two_primes_len2 l p2 p3 Hlprime Hp2 Hp3 Hprod_l).
			- subst a.
			  assert (Hprod_l : list_prod l = p1 * p3).
			  {
				assert (Htmp : list_prod l * p2 = (p1 * p3) * p2).
				{
					rewrite <- Heq.
					rewrite Hprod3.
					ring.
				}
				assert (Hp2_nz : p2 <> 0).
				{
					pose proof (prime_ge_2 _ Hp2).
					lia.
				}
				apply (Z.mul_reg_r (list_prod l) (p1 * p3) p2); auto.
			  }
			  exact (list_prod_eq_two_primes_len2 l p1 p3 Hlprime Hp1 Hp3 Hprod_l).
			- subst a.
			  assert (Hprod_l : list_prod l = p1 * p2).
			  {
				assert (Htmp : list_prod l * p3 = (p1 * p2) * p3).
				{
					rewrite <- Heq.
					rewrite Hprod3.
					ring.
				}
				assert (Hp3_nz : p3 <> 0).
				{
					pose proof (prime_ge_2 _ Hp3).
					lia.
				}
				apply (Z.mul_reg_r (list_prod l) (p1 * p2) p3); auto.
			  }
			  exact (list_prod_eq_two_primes_len2 l p1 p2 Hlprime Hp1 Hp2 Hprod_l).
		}
		assert (Hnum_eq_2 : num = 2) by lia.
		contradiction.
Qed.

Lemma proof_of_is_multiply_prime_return_wit_2 : is_multiply_prime_return_wit_2.
Proof.
	unfold is_multiply_prime_return_wit_2.
	left.
	intros.
	Intros.
	entailer!.
	unfold problem_75_spec_z.
	split.
	- intros Hnz.
		match goal with
		| Hinv : mp_outer_inv _ _ _ _ |- _ =>
			destruct Hinv as [Ha_ge2 [l [Hlprime [Hlen [Heq Hnodiv]]]]]
		end.
		assert (Hprime_a : prime a).
		{
			apply (prime_from_mp_outer_inv_exit a i).
			- exact Ha_ge2.
			- lia.
			- lia.
			- exact Hnodiv.
		}
		assert (Hlen2 : Z.of_nat (length l) = 2) by lia.
		destruct l.
		+ simpl in Hlen2. lia.
		+ destruct l.
		  * simpl in Hlen2. lia.
		  * destruct l.
			{ simpl in Hlen2.
			  pose proof (Forall_inv Hlprime) as Hp1.
			  pose proof (Forall_inv_tail Hlprime) as Ht.
			  pose proof (Forall_inv Ht) as Hp2.
			  exists z, z0, a.
			  split.
			  { exact Hp1. }
			  split.
			  { exact Hp2. }
			  split.
			  { exact Hprime_a. }
			  cbn [list_prod] in Heq.
			  ring_simplify in Heq.
			  exact Heq. }
			{ simpl in Hlen2. lia. }
	- intros Hex.
	  lia.
Qed.
