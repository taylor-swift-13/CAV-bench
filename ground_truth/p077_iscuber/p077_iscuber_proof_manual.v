Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p077_iscuber Require Import p077_iscuber_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p077_iscuber.
Local Open Scope sac.

Lemma cube_nonneg_le_compat :
  forall x y : Z, 0 <= x -> x < y -> x * x * x < y * y * y.
Proof.
  intros x y Hx Hlt.
  assert (Hfactor :
    y * y * y - x * x * x = (y - x) * (x * x + x * y + y * y)).
  { ring. }
  assert (0 < y - x) by lia.
  assert (0 <= x * x + x * y + y * y) by nia.
  nia.
Qed.

Lemma abs_cube :
  forall x : Z, Z.abs (x * x * x) = Z.abs x * Z.abs x * Z.abs x.
Proof.
  intro x.
  rewrite Z.abs_mul.
  rewrite Z.abs_mul.
  nia.
Qed.

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

Lemma proof_of_iscuber_entail_wit_2 : iscuber_entail_wit_2.
Proof.
  unfold iscuber_entail_wit_2.
  left.
  intros.
  Intros.
  entailer!.
  intros k [Hk0 Hklt].
  destruct (Z.lt_ge_cases k i) as [Hlt | Hge].
  - eapply PreH7; lia.
  - assert (k = i) by lia.
    subst k.
    lia.
Qed.

Lemma proof_of_iscuber_return_wit_1 : iscuber_return_wit_1.
Proof.
  unfold iscuber_return_wit_1, problem_77_spec_z.
  left.
  intros.
  Intros.
  entailer!.
  split.
  - intros Hfalse.
    contradiction.
  - intros Hcube.
    exfalso.
    destruct Hcube as [x Hx].
    assert (Habs : Z.abs a_pre = Z.abs x * Z.abs x * Z.abs x).
    { rewrite Hx. apply abs_cube. }
    assert (Hiabs : i * i * i > Z.abs a_pre) by (rewrite <- PreH2; exact PreH1).
    assert (Hxlt : Z.abs x < i).
    {
      assert (Hcube_lt : Z.abs x * Z.abs x * Z.abs x < i * i * i) by nia.
      destruct (Z_lt_ge_dec (Z.abs x) i) as [Hlt | Hge]; auto.
        assert (i * i * i <= Z.abs x * Z.abs x * Z.abs x).
        { destruct (Z.eq_dec (Z.abs x) i) as [Heq | Hneq].
        - subst. nia.
        - assert (Hilt : i < Z.abs x) by lia.
          pose proof (cube_nonneg_le_compat i (Z.abs x) PreH3 Hilt).
          nia. }
      nia.
    }
    pose proof (PreH5 (Z.abs x)) as Hneq.
    specialize (Hneq ltac:(lia)).
    apply Hneq.
    symmetry.
    exact Habs.
Qed.

Lemma proof_of_iscuber_return_wit_2 : iscuber_return_wit_2.
Proof.
  unfold iscuber_return_wit_2, problem_77_spec_z.
  left.
  intros.
  Intros.
  entailer!.
  split.
  - intros _.
    destruct (Z_lt_ge_dec a_pre 0) as [Hneg | Hnonneg].
    + exists (- i).
      assert (Hzabs : Z.abs a_pre = - a_pre) by (apply Z.abs_neq; lia).
      assert (Hiabs : i * i * i = Z.abs a_pre) by (rewrite PreH1; exact PreH2).
      rewrite <- Hiabs in Hzabs.
      nia.
    + exists i.
      assert (Hzabs : Z.abs a_pre = a_pre) by (apply Z.abs_eq; lia).
      assert (Hiabs : i * i * i = Z.abs a_pre) by (rewrite PreH1; exact PreH2).
      rewrite <- Hiabs in Hzabs.
      nia.
  - intros _. discriminate.
Qed.
