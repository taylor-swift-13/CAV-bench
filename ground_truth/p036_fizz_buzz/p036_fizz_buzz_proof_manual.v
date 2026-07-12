Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p036_fizz_buzz Require Import p036_fizz_buzz_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p036_fizz_buzz.
Local Open Scope sac.

(* BEGIN migrated companion-spec proofs *)
Module MigratedCompanionProofs.
Local Open Scope bool_scope.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope nat_scope.



Lemma count_digit_7_aux_stable : forall k fuel,
  (k <= fuel)%nat ->
  count_digit_7_aux k fuel = count_digit_7 k.
Proof.
  refine (well_founded_induction
            lt_wf
            (fun k => forall fuel, (k <= fuel)%nat -> count_digit_7_aux k fuel = count_digit_7 k)
            _).
  intros k IH fuel Hle.
  destruct k as [| k'].
  - unfold count_digit_7.
    destruct fuel; reflexivity.
  - destruct fuel as [| fuel']; [lia|].
    unfold count_digit_7.
    simpl.
    f_equal.
    specialize (IH (Nat.div (S k') 10)).
    assert (Hdiv : (Nat.div (S k') 10 < S k')%nat).
    { apply Nat.div_lt; lia. }
    specialize (IH Hdiv).
    transitivity (count_digit_7 (Nat.div (S k') 10)).
    + apply IH.
      lia.
    + symmetry.
      apply IH.
      lia.
Qed.

Lemma count_digit_7_step_hit_nat : forall k,
  (0 < k)%nat ->
  (Nat.modulo k 10 = 7)%nat ->
  count_digit_7 k = (1 + count_digit_7 (Nat.div k 10))%nat.
Proof.
  intros [| k] Hpos Hmod; [lia|].
  unfold count_digit_7.
  simpl.
  destruct (Nat.eqb (Nat.modulo (S k) 10) 7) eqn:Htest.
  - apply Nat.eqb_eq in Htest.
    replace
      (if
        match snd (Nat.divmod k 9%nat 0%nat 8%nat) with
        | 0%nat => 9%nat | 1%nat => 8%nat | 2%nat => 7%nat | 3%nat => 6%nat | 4%nat => 5%nat
        | 5%nat => 4%nat | 6%nat => 3%nat | 7%nat => 2%nat | 8%nat => 1%nat
        | S (S (S (S (S (S (S (S (S _)))))))) => 0%nat
        end =? 7%nat
       then 1%nat
       else 0%nat)
      with (if Nat.eqb (Nat.modulo (S k) 10%nat) 7%nat then 1%nat else 0%nat) by reflexivity.
    rewrite Htest.
    simpl.
    replace (count_digit_7_aux (fst (Nat.divmod k 9 0 8)) k)
      with (count_digit_7_aux (Nat.div (S k) 10) k) by reflexivity.
    replace
      (count_digit_7_aux (fst (Nat.divmod k 9 0 8)) (fst (Nat.divmod k 9 0 8)))
      with (count_digit_7_aux (Nat.div (S k) 10) (Nat.div (S k) 10))
      by reflexivity.
    rewrite (count_digit_7_aux_stable (Nat.div (S k) 10) k).
    + reflexivity.
    + apply Nat.lt_succ_r.
      apply Nat.div_lt; lia.
  - apply Nat.eqb_neq in Htest.
    contradiction.
Qed.

Lemma count_digit_7_step_miss_nat : forall k,
  (0 < k)%nat ->
  (Nat.modulo k 10 <> 7)%nat ->
  count_digit_7 k = count_digit_7 (Nat.div k 10).
Proof.
  intros [| k] Hpos Hmod; [lia|].
  unfold count_digit_7.
  simpl.
  destruct (Nat.eqb (Nat.modulo (S k) 10) 7) eqn:Htest.
  - apply Nat.eqb_eq in Htest.
    contradiction.
  - replace
      (if
        match snd (Nat.divmod k 9 0 8) with
        | 0 => 9 | 1 => 8 | 2 => 7 | 3 => 6 | 4 => 5
        | 5 => 4 | 6 => 3 | 7 => 2 | 8 => 1
        | S (S (S (S (S (S (S (S (S _)))))))) => 0
        end =? 7
       then 1
       else 0)
      with (if Nat.eqb (Nat.modulo (S k) 10) 7 then 1 else 0) by reflexivity.
    rewrite Htest.
    simpl.
    replace (count_digit_7_aux (fst (Nat.divmod k 9 0 8)) k)
      with (count_digit_7_aux (Nat.div (S k) 10) k) by reflexivity.
    replace
      (count_digit_7_aux (fst (Nat.divmod k 9 0 8)) (fst (Nat.divmod k 9 0 8)))
      with (count_digit_7_aux (Nat.div (S k) 10) (Nat.div (S k) 10))
      by reflexivity.
    rewrite (count_digit_7_aux_stable (Nat.div (S k) 10) k).
    + reflexivity.
    + apply Nat.lt_succ_r.
      apply Nat.div_lt; lia.
Qed.

Lemma count_digit_7_le_self : forall k,
  (count_digit_7 k <= k)%nat.
Proof.
  refine (well_founded_induction
            lt_wf
            (fun k => (count_digit_7 k <= k)%nat)
            _).
  intros k IH.
  destruct k as [| k].
  - reflexivity.
  - destruct (Nat.eq_dec (Nat.modulo (S k) 10) 7) as [Hhit | Hmiss].
    + rewrite count_digit_7_step_hit_nat by lia.
      assert (Hdivlt : (Nat.div (S k) 10 < S k)%nat).
      { apply Nat.div_lt; lia. }
      specialize (IH (Nat.div (S k) 10) Hdivlt).
      lia.
    + rewrite count_digit_7_step_miss_nat by lia.
      assert (Hdivlt : (Nat.div (S k) 10 < S k)%nat).
      { apply Nat.div_lt; lia. }
      specialize (IH (Nat.div (S k) 10) Hdivlt).
      lia.
Qed.
Local Open Scope Z_scope.


Lemma count_digit7_nonneg : forall q,
  0 <= count_digit7 q.
Proof.
  intro q.
  unfold count_digit7.
  lia.
Qed.

Lemma count_digit7_le_self : forall q,
  0 <= q ->
  count_digit7 q <= q.
Proof.
  intros q Hq.
  unfold count_digit7.
  rewrite <- (Z2Nat.id q) at 2 by lia.
  apply Nat2Z.inj_le.
  apply count_digit_7_le_self.
Qed.

Lemma count_digit7_step_hit : forall q,
  0 < q ->
  q mod 10 = 7 ->
  count_digit7 q = 1 + count_digit7 (q / 10).
Proof.
  intros q Hqpos Hmod.
  unfold count_digit7.
  rewrite Z2Nat.inj_div by lia.
  assert (Hnatmod : (Nat.modulo (Z.to_nat q) 10 = 7)%nat).
  {
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod.
    rewrite Z2Nat.id by lia.
    exact Hmod.
  }
  rewrite count_digit_7_step_hit_nat.
  2: {
    rewrite <- Z2Nat.inj_0.
    apply Z2Nat.inj_lt; lia.
  }
  2: exact Hnatmod.
  rewrite Nat2Z.inj_add.
  simpl.
  lia.
Qed.

Lemma count_digit7_step_miss : forall q,
  0 < q ->
  q mod 10 <> 7 ->
  count_digit7 q = count_digit7 (q / 10).
Proof.
  intros q Hqpos Hmod.
  unfold count_digit7.
  rewrite Z2Nat.inj_div by lia.
  rewrite count_digit_7_step_miss_nat.
  - reflexivity.
  - rewrite <- Z2Nat.inj_0.
    apply Z2Nat.inj_lt; lia.
  - intro Hnatmod.
    apply Hmod.
    apply (f_equal Z.of_nat) in Hnatmod.
    rewrite Nat2Z.inj_mod in Hnatmod.
    rewrite Z2Nat.id in Hnatmod by lia.
    exact Hnatmod.
Qed.

Lemma fizz_buzz_impl_step_nat : forall n,
  fizz_buzz_impl (S n) =
    (fizz_buzz_impl n +
      (if (Nat.eqb (Nat.modulo n 11) 0) || (Nat.eqb (Nat.modulo n 13) 0)
       then count_digit_7 n
       else 0))%nat.
Proof.
  intro n.
  unfold fizz_buzz_impl.
  rewrite seq_S.
  rewrite fold_left_app.
  simpl.
  lia.
Qed.

Lemma fizzbuzz_upto_0 :
  fizzbuzz_upto 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma fizzbuzz_upto_step_div11 : forall i,
  0 <= i ->
  i mod 11 = 0 ->
  fizzbuzz_upto (i + 1) = fizzbuzz_upto i + count_digit7 i.
Proof.
  intros i Hi Hmod.
  unfold fizzbuzz_upto, count_digit7.
  rewrite !Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  rewrite fizz_buzz_impl_step_nat.
  assert (Hmod11 : Nat.eqb (Nat.modulo (Z.to_nat i) 11) 0 = true).
  {
    apply Nat.eqb_eq.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod.
    rewrite Z2Nat.id by lia.
    exact Hmod.
  }
  rewrite Hmod11.
  simpl.
  lia.
Qed.

Lemma fizzbuzz_upto_step_div13 : forall i,
  0 <= i ->
  i mod 13 = 0 ->
  fizzbuzz_upto (i + 1) = fizzbuzz_upto i + count_digit7 i.
Proof.
  intros i Hi Hmod.
  unfold fizzbuzz_upto, count_digit7.
  rewrite !Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  rewrite fizz_buzz_impl_step_nat.
  assert (Hmod13 : Nat.eqb (Nat.modulo (Z.to_nat i) 13) 0 = true).
  {
    apply Nat.eqb_eq.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod.
    rewrite Z2Nat.id by lia.
    exact Hmod.
  }
  rewrite Hmod13.
  destruct (Nat.eqb (Nat.modulo (Z.to_nat i) 11) 0); simpl; lia.
Qed.

Lemma fizzbuzz_upto_step_nondiv : forall i,
  0 <= i ->
  i mod 11 <> 0 ->
  i mod 13 <> 0 ->
  fizzbuzz_upto (i + 1) = fizzbuzz_upto i.
Proof.
  intros i Hi H11 H13.
  unfold fizzbuzz_upto.
  rewrite !Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  rewrite fizz_buzz_impl_step_nat.
  assert (Hmod11 : Nat.eqb (Nat.modulo (Z.to_nat i) 11) 0 = false).
  {
    apply Nat.eqb_neq.
    intro Hnat.
    apply H11.
    apply (f_equal Z.of_nat) in Hnat.
    rewrite Nat2Z.inj_mod in Hnat.
    rewrite Z2Nat.id in Hnat by lia.
    exact Hnat.
  }
  assert (Hmod13 : Nat.eqb (Nat.modulo (Z.to_nat i) 13) 0 = false).
  {
    apply Nat.eqb_neq.
    intro Hnat.
    apply H13.
    apply (f_equal Z.of_nat) in Hnat.
    rewrite Nat2Z.inj_mod in Hnat.
    rewrite Z2Nat.id in Hnat by lia.
    exact Hnat.
  }
  rewrite Hmod11, Hmod13.
  simpl.
  lia.
Qed.

Lemma fizz_buzz_impl_le_square_nat : forall n,
  (fizz_buzz_impl n <= n * n)%nat.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite fizz_buzz_impl_step_nat.
    assert (Hdigit : (count_digit_7 n <= n)%nat).
    { apply count_digit_7_le_self. }
    destruct ((Nat.eqb (Nat.modulo n 11) 0) || (Nat.eqb (Nat.modulo n 13) 0)); simpl; lia.
Qed.

Lemma fizzbuzz_upto_le_square : forall i,
  0 <= i ->
  fizzbuzz_upto i <= i * i.
Proof.
  intros i Hi.
  unfold fizzbuzz_upto.
  rewrite <- (Z2Nat.id i) at 2 by lia.
  rewrite <- (Z2Nat.id i) at 3 by lia.
  rewrite <- Nat2Z.inj_mul.
  apply Nat2Z.inj_le.
  apply fizz_buzz_impl_le_square_nat.
Qed.
End MigratedCompanionProofs.
Export MigratedCompanionProofs.
(* END migrated companion-spec proofs *)

Lemma proof_of_fizz_buzz_safety_wit_10 : fizz_buzz_safety_wit_10.
Proof.
  unfold fizz_buzz_safety_wit_10.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hqmod : q mod 10 = 7).
  {
    rewrite <- (Z.rem_mod_nonneg q 10) by lia.
    exact PreH1.
  }
  assert (Hqdigit : count_digit7 q = 1 + count_digit7 (q / 10)).
  {
    apply count_digit7_step_hit.
    - lia.
    - exact Hqmod.
  }
  assert (Hnonneg : 0 <= count_digit7 (q / 10)).
  { apply count_digit7_nonneg. }
  assert (Hbound : count + 1 <= i_2 * (i_2 + 1)).
  { rewrite Hqdigit in PreH10. lia. }
  assert (Hi2bound : i_2 * (i_2 + 1) <= 46340 * 46341) by nia.
  nia.
Qed.

Lemma proof_of_fizz_buzz_safety_wit_23 : fizz_buzz_safety_wit_23.
Proof.
  unfold fizz_buzz_safety_wit_23.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hqmod : q mod 10 = 7).
  {
    rewrite <- (Z.rem_mod_nonneg q 10) by lia.
    exact PreH1.
  }
  assert (Hqdigit : count_digit7 q = 1 + count_digit7 (q / 10)).
  {
    apply count_digit7_step_hit.
    - lia.
    - exact Hqmod.
  }
  assert (Hnonneg : 0 <= count_digit7 (q / 10)).
  { apply count_digit7_nonneg. }
  assert (Hbound : count + 1 <= i_2 * (i_2 + 1)).
  { rewrite Hqdigit in PreH11. lia. }
  assert (Hi2bound : i_2 * (i_2 + 1) <= 46340 * 46341) by nia.
  nia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_1 : fizz_buzz_entail_wit_1.
Proof.
  unfold fizz_buzz_entail_wit_1.
  left.
  intros.
  Intros.
  entailer!.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_2 : fizz_buzz_entail_wit_2.
Proof.
  unfold fizz_buzz_entail_wit_2.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hdigit : count_digit7 i <= i) by (apply count_digit7_le_self; lia).
  lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_1 : fizz_buzz_entail_wit_3_1.
Proof.
  unfold fizz_buzz_entail_wit_3_1.
  left.
  intros.
  Intros.
  entailer!.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact PreH1. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof PreH10 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Hbound.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact PreH1. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof PreH9 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_3_2 : fizz_buzz_entail_wit_3_2.
Proof.
  unfold fizz_buzz_entail_wit_3_2.
  left.
  intros.
  Intros.
  entailer!.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply PreH1.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof PreH10 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Hbound.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply PreH1.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof PreH9 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_4 : fizz_buzz_entail_wit_4.
Proof.
  unfold fizz_buzz_entail_wit_4.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hdigit : count_digit7 i <= i) by (apply count_digit7_le_self; lia).
  lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_5_1 : fizz_buzz_entail_wit_5_1.
Proof.
  unfold fizz_buzz_entail_wit_5_1.
  left.
  intros.
  Intros.
  entailer!.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact PreH1. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof PreH11 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Hbound.
  - assert (Hqmod : q mod 10 = 7).
    { rewrite <- (Z.rem_mod_nonneg q 10) by lia. exact PreH1. }
    assert (Hstep : count_digit7 q = 1 + count_digit7 (q / 10)).
    { apply count_digit7_step_hit; [lia | exact Hqmod]. }
    pose proof PreH10 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    replace
      (count_2 + 1 + count_digit7 (q / 10))
      with (count_2 + (1 + count_digit7 (q / 10))) by lia.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_5_2 : fizz_buzz_entail_wit_5_2.
Proof.
  unfold fizz_buzz_entail_wit_5_2.
  left.
  intros.
  Intros.
  entailer!.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply PreH1.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof PreH11 as Hbound.
    rewrite Hstep in Hbound.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Hbound.
  - assert (Hqmiss : q mod 10 <> 7).
    {
      intro Hcontra.
      apply PreH1.
      rewrite <- (Z.rem_mod_nonneg q 10) in Hcontra by lia.
      exact Hcontra.
    }
    assert (Hstep : count_digit7 q = count_digit7 (q / 10)).
    { apply count_digit7_step_miss; [lia | exact Hqmiss]. }
    pose proof PreH10 as Heq.
    rewrite Hstep in Heq.
    assert (Hqquot : q ÷ 10 = q / 10) by (apply Z.quot_div_nonneg; lia).
    rewrite Hqquot.
    exact Heq.
  - apply Z.quot_pos; lia.
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_1 : fizz_buzz_entail_wit_6_1.
Proof.
  unfold fizz_buzz_entail_wit_6_1.
  left.
  intros.
  Intros.
  entailer!;
    [ apply store_int_undef_store_int
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in PreH9;
       replace (count + 0) with count in PreH9 by lia;
       nia)
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in PreH8;
       replace (count + 0) with count in PreH8 by lia;
       assert (Himod : i mod 11 = 0) by (rewrite <- (Z.rem_mod_nonneg i 11) by lia; exact PreH6);
       pose proof (fizzbuzz_upto_step_div11 i PreH3 Himod) as Hstepfb;
       rewrite <- Hstepfb in PreH8;
       exact PreH8) ].
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_2 : fizz_buzz_entail_wit_6_2.
Proof.
  unfold fizz_buzz_entail_wit_6_2.
  left.
  intros.
  Intros.
  entailer!;
    [ apply store_int_undef_store_int
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in PreH10;
       replace (count + 0) with count in PreH10 by lia;
       nia)
    | (assert (Hq : q = 0) by lia;
       subst q;
       change (count_digit7 0) with 0 in PreH9;
       replace (count + 0) with count in PreH9 by lia;
       assert (Himod : i mod 13 = 0) by (rewrite <- (Z.rem_mod_nonneg i 13) by lia; exact PreH6);
       pose proof (fizzbuzz_upto_step_div13 i PreH3 Himod) as Hstepfb;
       rewrite <- Hstepfb in PreH9;
       exact PreH9) ].
Qed.

Lemma proof_of_fizz_buzz_entail_wit_6_3 : fizz_buzz_entail_wit_6_3.
Proof.
  unfold fizz_buzz_entail_wit_6_3.
  left.
  intros.
  Intros.
  entailer!.
  assert (Hmod11 : i mod 11 <> 0).
  {
    intro Hcontra.
    apply PreH2.
    rewrite <- (Z.rem_mod_nonneg i 11) in Hcontra by lia.
    exact Hcontra.
  }
  assert (Hmod13 : i mod 13 <> 0).
  {
    intro Hcontra.
    apply PreH1.
    rewrite <- (Z.rem_mod_nonneg i 13) in Hcontra by lia.
    exact Hcontra.
  }
  pose proof (fizzbuzz_upto_step_nondiv i PreH4 Hmod11 Hmod13) as Hstep.
  rewrite Hstep.
  exact PreH6.
Qed.

Lemma proof_of_fizz_buzz_return_wit_1 : fizz_buzz_return_wit_1.
Proof.
  unfold fizz_buzz_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  unfold problem_36_spec_z, problem_36_spec.
  assert (Hi_eq : i = n_pre) by lia.
  subst i.
  subst count.
  unfold fizzbuzz_upto.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
