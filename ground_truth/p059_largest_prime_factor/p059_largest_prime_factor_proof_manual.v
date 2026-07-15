Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
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
From SimpleC.EE.CAV.ground_truth_p059_largest_prime_factor Require Import p059_largest_prime_factor_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p059_largest_prime_factor.
Local Open Scope sac.

(* Auxiliary number-theory lemmas migrated from the QCP 2.0.4 proof bundle.
   They live in the manual proof artifact so the companion specification file
   remains definition-only. *)
Lemma lpf_inv_after_not_div :
  forall n_pre n i : Z,
  n mod i <> 0 ->
  i >= 2 ->
  lpf_while_inv n_pre n i ->
  lpf_inv n_pre n (i + 1).
Proof.
  intros n_pre n i Hmod_ne Hi Hwhile.
  unfold lpf_while_inv in Hwhile.
  destruct Hwhile as [Himax [Hn_ge2 [Hi_le_n [Hmod [Hsmall [Hbound Hlarge]]]]]].
  unfold lpf_inv.
  split; [exact Hn_ge2|].
  split; [exact Hmod|].
  split.
  - intros p Hp_prime Hp_ge2 Hp_lt.
    destruct (Z_lt_ge_dec p i) as [Hp_lt_i | Hp_ge_i].
    + apply Hsmall; auto.
    + assert (Hp_eq_i : p = i) by lia.
      subst p.
      left.
      intro Hdiv_i_n.
      apply Hmod_ne.
      apply (proj2 (Z.mod_divide n i ltac:(lia))).
      exact Hdiv_i_n.
  - split.
    + intros p Hp_prime Hp_ge2 Hp_lt Hnot_div.
      destruct (Z_lt_ge_dec p i) as [Hp_lt_i | Hp_ge_i].
      * apply Hbound; auto.
      * assert (p = i) by lia.
        subst p.
        lia.
    + intros q Hq_prime Hq_ge Hq_div.
      apply Hlarge; auto; lia.
Qed.

Lemma lpf_inv_after_le_mod0 :
  forall n_pre n i : Z,
  n <= i ->
  n mod i = 0 ->
  i >= 2 ->
  lpf_while_inv n_pre n i ->
  lpf_inv n_pre n (i + 1).
Proof.
  intros n_pre n i Hn_le_i Hmod0 Hi Hwhile.
  unfold lpf_while_inv in Hwhile.
  destruct Hwhile as [Himax [Hn_ge2 [Hi_le_n [Hmod [Hsmall [Hbound Hlarge]]]]]].
  assert (Hn_eq_i : n = i) by lia.
  subst n.
  unfold lpf_inv.
  split; [lia|].
  split; [exact Hmod|].
  split.
  - intros p Hp_prime Hp_ge2 Hp_lt.
    destruct (Z_lt_ge_dec p i) as [Hp_lt_i | Hp_ge_i].
    + apply Hsmall; auto.
    + assert (p = i) by lia.
      subst p.
      right; reflexivity.
  - split.
    + intros p Hp_prime Hp_ge2 Hp_lt Hnot_div.
      destruct (Z_lt_ge_dec p i) as [Hp_lt_i | Hp_ge_i].
      * apply Hbound; auto.
      * assert (p = i) by lia.
        subst p.
        lia.
    + intros q Hq_prime Hq_ge Hq_div.
      apply Hlarge; auto; lia.
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
  assert (Hd_pos : 0 < d) by lia.
  assert (Hk_pos : 0 < k) by (subst n; nia).
  assert (Hk_gt1 : 1 < k) by (subst n; nia).
  set (m := Z.min d k).
  assert (Hm_lt_n : m < n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_gt1 : 1 < m).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia; lia.
    - rewrite Z.min_r by lia; lia.
  }
  assert (Hm_div_n : Z.divide m n).
  {
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    - rewrite Z.min_l by lia. exists k. exact Hn_eq.
    - rewrite Z.min_r by lia. exists d. subst n. ring.
  }
  destruct (prime_dec m) as [Hm_prime|Hm_not_prime].
  - exists m. split; [exact Hm_prime|].
    split; [exact Hm_div_n|].
    unfold m.
    destruct (Z_le_gt_dec d k) as [Hdk|Hdk].
    + rewrite Z.min_l by lia. subst n. nia.
    + rewrite Z.min_r by lia. subst n. nia.
  - specialize (IH m).
    assert (Hm_range : 1 <= m < n) by lia.
    specialize (IH Hm_range).
    assert (Hm_ge2 : 2 <= m) by lia.
    specialize (IH Hm_ge2 Hm_not_prime).
    destruct IH as [p [Hp_prime [Hp_div_m Hp_sq_le_m]]].
    exists p. split; [exact Hp_prime|].
    split.
    + eapply Z.divide_trans; eauto.
    + lia.
Qed.

Lemma div_factor_ge_candidate :
  forall n i : Z,
  2 <= i ->
  n > i ->
  n mod i = 0 ->
  (forall p : Z, prime p -> 2 <= p -> p < i -> ~ Z.divide p n \/ n = p) ->
  i <= n / i.
Proof.
  intros n i Hi Hn_gt_i Hmod Hsmall.
  assert (Hi_pos : 0 < i) by lia.
  assert (Hn_eq : n = (n / i) * i).
  {
    pose proof (Z.div_mod n i ltac:(lia)) as Hdiv.
    nia.
  }
  assert (Hd_gt1 : 1 < n / i) by nia.
  destruct (Z_lt_ge_dec (n / i) i) as [Hd_lt_i | Hd_ge_i]; [|lia].
  assert (Hd_ge2 : 2 <= n / i) by lia.
  destruct (prime_dec (n / i)) as [Hd_prime | Hd_not_prime].
  - specialize (Hsmall (n / i) Hd_prime Hd_ge2 Hd_lt_i).
    destruct Hsmall as [Hnot_div | Hn_eq_d].
    + exfalso.
      apply Hnot_div.
      exists i. nia.
    + lia.
  - destruct (composite_has_small_prime_divisor (n / i) Hd_ge2 Hd_not_prime)
      as [p [Hp_prime [Hp_div_d Hp_sq_le_d]]].
    assert (Hp_ge2 : 2 <= p) by (apply prime_ge_2; exact Hp_prime).
    assert (Hp_le_d : p <= n / i) by nia.
    assert (Hp_lt_i : p < i) by lia.
    assert (Hp_div_n : Z.divide p n).
    {
      destruct Hp_div_d as [k Hk].
      exists (i * k). nia.
    }
    specialize (Hsmall p Hp_prime Hp_ge2 Hp_lt_i).
    destruct Hsmall as [Hnot_div | Hn_eq_p].
    + contradiction.
    + lia.
Qed.

Lemma lpf_while_inv_div_step :
  forall n_pre n i : Z,
  i >= 2 ->
  n > i ->
  n mod i = 0 ->
  lpf_while_inv n_pre n i ->
  lpf_while_inv n_pre (n / i) i.
Proof.
  intros n_pre n i Hi Hn_gt_i Hmod0 Hwhile.
  unfold lpf_while_inv in Hwhile.
  destruct Hwhile as [Himax [Hn_ge2 [Hi_le_n [Hmod [Hsmall [Hbound Hlarge]]]]]].
  assert (Hi_pos : 0 < i) by lia.
  assert (Hn_eq : n = (n / i) * i).
  {
    pose proof (Z.div_mod n i ltac:(lia)) as Hdiv.
    nia.
  }
  assert (Hi_le_div : i <= n / i).
  {
    apply (div_factor_ge_candidate n i); auto; lia.
  }
  assert (Hdiv_ge2 : 2 <= n / i) by lia.
  unfold lpf_while_inv.
  split; [exact Himax|].
  split; [lia|].
  split; [lia|].
  split.
  - assert (Hn_div_pre : Z.divide n n_pre).
    {
      apply Z.mod_divide in Hmod; [exact Hmod|lia].
    }
    assert (Hdiv_div_n : Z.divide (n / i) n).
    {
      exists i. nia.
    }
    assert (Hdiv_div_pre : Z.divide (n / i) n_pre).
    {
      eapply Z.divide_trans; eauto.
    }
    apply (proj2 (Z.mod_divide n_pre (n / i) ltac:(lia))).
    exact Hdiv_div_pre.
  - split.
    + intros p Hp_prime Hp_ge2 Hp_lt_i.
      assert (Hnot_div_n : ~ Z.divide p n).
      {
        specialize (Hsmall p Hp_prime Hp_ge2 Hp_lt_i).
        destruct Hsmall as [Hnot_div | Hn_eq_p].
        - exact Hnot_div.
        - lia.
      }
      left.
      intro Hp_div_q.
      apply Hnot_div_n.
      destruct Hp_div_q as [k Hk].
      exists (i * k). nia.
    + split.
      * intros p Hp_prime Hp_ge2 Hp_lt_i Hnot_div_q.
        lia.
      * intros q Hq_prime Hq_gt_i Hq_div_pre.
        assert (Hq_div_n : Z.divide q n).
        {
          apply Hlarge; auto.
        }
        rewrite Hn_eq in Hq_div_n.
        destruct (prime_mult q Hq_prime (n / i) i Hq_div_n) as [Hq_div_q | Hq_div_i].
        -- exact Hq_div_q.
        -- assert (q <= i).
           {
             apply Z.divide_pos_le; [lia | exact Hq_div_i].
           }
           lia.
Qed.

Lemma div_square_lt_from_exit :
  forall n i : Z,
  2 <= i ->
  i > n / i ->
  n < i * i.
Proof.
  intros n i Hi2 Hexit.
  assert (Hi_pos : 0 < i) by lia.
  pose proof (Z.div_mod n i (not_eq_sym (Z.lt_neq _ _ Hi_pos))) as Hmod.
  assert (Hr_bound : 0 <= n mod i < i) by (apply Z.mod_pos_bound; lia).
  destruct Hr_bound as [_ Hr_lt].
  nia.
Qed.

Lemma lpf_spec_from_exit :
  forall n_pre n i : Z,
  problem_59_pre n_pre ->
  2 <= n_pre ->
  n_pre <= 2147483647 ->
  2 <= i ->
  i > n / i ->
  lpf_inv n_pre n i ->
  problem_59_spec n_pre n.
Proof.
  intros n_pre n i _ _ _ Hi2 Hexit Hinv.
  destruct Hinv as [Hn2 [Hmod [Hsmall_div [Hsmall_bound Hlarge_div]]]].
  assert (Hn_div_npre : Z.divide n n_pre).
  {
    apply Z.mod_divide in Hmod; [exact Hmod|lia].
  }
  assert (Hprime_n : prime n).
  {
    assert (Hn2_le : 2 <= n) by lia.
    destruct (prime_dec n) as [Hprime|Hnot_prime]; [exact Hprime|].
    exfalso.
    destruct (composite_has_small_prime_divisor n Hn2_le Hnot_prime) as [p [Hp_prime [Hp_div_n Hp_sq_le_n]]].
    assert (Hn_lt_ii : n < i * i) by (apply div_square_lt_from_exit; auto).
    assert (Hp_ge2 : 2 <= p) by (apply prime_ge_2; exact Hp_prime).
    assert (Hp_lt_i : p < i).
    {
      apply Z.nle_gt; intros Hp_ge_i.
      assert (Hi_sq_le_p_sq : i * i <= p * p) by nia.
      lia.
    }
    specialize (Hsmall_div p Hp_prime Hp_ge2 Hp_lt_i).
    destruct Hsmall_div as [Hp_not_div_n | Hn_eq_p].
    - contradiction.
    - subst n. contradiction.
  }
  split.
  - exact Hprime_n.
  - split.
    + exact Hn_div_npre.
    + intros q [Hq_prime Hq_div_npre].
      destruct (Z_lt_ge_dec q i) as [Hq_lt_i | Hq_ge_i].
      * assert (Hq_ge2 : 2 <= q) by (apply prime_ge_2; exact Hq_prime).
        specialize (Hsmall_div q Hq_prime Hq_ge2 Hq_lt_i).
        destruct Hsmall_div as [Hq_not_div_n | Hn_eq_q].
        -- apply Hsmall_bound; auto.
        -- subst q. lia.
      * assert (Hq_div_n : Z.divide q n).
        {
          apply Hlarge_div; auto.
        }
        apply Z.divide_pos_le.
        -- lia.
        -- exact Hq_div_n.
Qed.

Lemma proof_of_largest_prime_factor_safety_wit_5 : largest_prime_factor_safety_wit_5.
Proof.
	unfold largest_prime_factor_safety_wit_5.
	left.
	intros.
	Intros.
	entailer!.
	match goal with
	| Hinv : lpf_while_inv _ _ _ |- _ =>
		unfold lpf_while_inv in Hinv
	end.
	lia.
Qed.

Lemma proof_of_largest_prime_factor_safety_wit_6 : largest_prime_factor_safety_wit_6.
Proof.
	unfold largest_prime_factor_safety_wit_6.
	left.
	intros.
	Intros.
	entailer!.
	unfold lpf_while_inv in PreH4.
	lia.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_1 : largest_prime_factor_entail_wit_1.
Proof.
	unfold largest_prime_factor_entail_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	unfold lpf_inv.
	split.
	- lia.
	- split.
	  + rewrite Z.mod_same by lia.
	    reflexivity.
	  + split.
	    * intros p Hpprime Hpge2 Hplt2.
	      lia.
	    * split.
	      { intros p Hpprime Hpge2 Hplt2 Hndiv.
	        lia. }
	      intros q Hqprime Hqge2 Hqdiv.
	      exact Hqdiv.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_2 : largest_prime_factor_entail_wit_2.
Proof.
	unfold largest_prime_factor_entail_wit_2.
	left.
	intros.
	Intros.
	entailer!.
	unfold lpf_inv in PreH3.
	destruct PreH3 as (Hn_ge2 & Hmod & Hsmall & Hbound & Hlarge).
	assert (Hi_ge2 : 2 <= i) by lia.
	assert (Hnpre_ge2 : 2 <= n_pre) by lia.
	assert (Hnpre_max : n_pre <= INT_MAX) by lia.
	pose proof (Zquot_Zdiv_pos n i ltac:(lia) ltac:(lia)) as Hq.
	rewrite Hq in PreH1.
	assert (Hn_le_npre : n <= n_pre).
	{
		destruct (Z_le_gt_dec n n_pre) as [Hle | Hgt].
		- exact Hle.
		- assert (0 <= n_pre < n) by lia.
		  rewrite Z.mod_small in Hmod by lia.
		  lia.
	}
	assert (Hi1_le_n : i + 1 <= n).
	{
		assert (Hi_pos : 0 < i) by lia.
		assert (Hdiv_mul_le : (n / i) * i <= n).
		{
			pose proof (Z.div_mod n i ltac:(lia)) as Hdiv.
			rewrite Z.mul_comm in Hdiv.
			assert (0 <= n mod i) by (apply Z.mod_pos_bound; lia).
			lia.
		}
		assert (Hi_mul_le : i * i <= (n / i) * i).
		{
			apply Z.mul_le_mono_nonneg_r; lia.
		}
		assert (Hi2_le_n : i * i <= n) by lia.
		assert (Hi1_le_i2 : i + 1 <= i * i) by nia.
		lia.
	}
	unfold lpf_while_inv.
	split.
	- lia.
	- split.
	  + exact Hn_ge2.
	  + split.
	    * lia.
	    * split.
	      { exact Hmod. }
	      split.
	      { exact Hsmall. }
	      split.
	      { exact Hbound. }
	      intros q Hprime Hqi Hdiv.
	      eapply Hlarge; eauto; lia.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_3_1 : largest_prime_factor_entail_wit_3_1.
Proof.
	unfold largest_prime_factor_entail_wit_3_1.
	left.
	intros.
	Intros.
	entailer!.
	pose proof PreH3 as Hwhile.
	unfold lpf_while_inv in Hwhile.
	destruct Hwhile as [_ [Hn_ge2 _]].
	apply lpf_inv_after_not_div.
	- rewrite <- Z.rem_mod_nonneg by lia.
	  exact PreH1.
	- lia.
	- exact PreH3.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_3_2 : largest_prime_factor_entail_wit_3_2.
Proof.
	unfold largest_prime_factor_entail_wit_3_2.
	left.
	intros.
	Intros.
	entailer!.
	pose proof PreH4 as Hwhile.
	unfold lpf_while_inv in Hwhile.
	destruct Hwhile as [_ [Hn_ge2 _]].
	apply lpf_inv_after_le_mod0.
	- lia.
	- rewrite <- Z.rem_mod_nonneg by lia.
	  exact PreH2.
	- lia.
	- exact PreH4.
Qed.

Lemma proof_of_largest_prime_factor_entail_wit_4 : largest_prime_factor_entail_wit_4.
Proof.
	unfold largest_prime_factor_entail_wit_4.
	left.
	intros.
	Intros.
	entailer!.
	pose proof PreH4 as Hwhile.
	unfold lpf_while_inv in Hwhile.
	destruct Hwhile as [_ [Hn2_ge2 _]].
	pose proof (Zquot_Zdiv_pos n_2 i_2 ltac:(lia) ltac:(lia)) as Hquot.
	rewrite Hquot.
	apply lpf_while_inv_div_step.
	- lia.
	- lia.
	- rewrite <- Z.rem_mod_nonneg by lia.
	  exact PreH2.
	- exact PreH4.
Qed.

Lemma proof_of_largest_prime_factor_return_wit_1 : largest_prime_factor_return_wit_1.
Proof.
	unfold largest_prime_factor_return_wit_1.
	left.
	intros.
	Intros.
	entailer!.
	pose proof PreH3 as Hinv.
	unfold lpf_inv in Hinv.
	destruct Hinv as (Hn_ge2 & _).
	pose proof (Zquot_Zdiv_pos n i ltac:(lia) ltac:(lia)) as Hq.
	rewrite Hq in PreH1.
	eapply (lpf_spec_from_exit n_pre n i); eauto.
Qed.
