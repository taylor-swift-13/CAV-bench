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
From SimpleC.EE.CAV.ground_truth_p049_modp Require Import p049_modp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p049_modp.
Local Open Scope sac.

(* Overflow safety: out = 2^i % p_pre < p_pre, and p_pre * 2 <= INT_MAX,
   so out * 2 < p_pre * 2 <= INT_MAX, and out >= 0 so out * 2 >= 0 > INT_MIN *)
Lemma proof_of_modp_safety_wit_5 : modp_safety_wit_5.
Proof.
  unfold modp_safety_wit_5.
  left; intros.
  apply _derivable1_andp_intros; apply dump_spatial_left.
  - subst out.
    pose proof (Z.rem_bound_pos (2 ^ i) p_pre ltac:(apply Z.pow_nonneg; lia) ltac:(lia)).
    nia.
  - subst out.
    pose proof (Z.rem_bound_pos (2 ^ i) p_pre ltac:(apply Z.pow_nonneg; lia) ltac:(lia)).
    nia.
Qed.

Lemma proof_of_modp_entail_wit_1 : modp_entail_wit_1.
Proof.
  unfold modp_entail_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  rewrite Z.pow_0_r.
  rewrite Z.rem_1_l by lia.
  reflexivity.
Qed.

Lemma proof_of_modp_entail_wit_2 : modp_entail_wit_2.
Proof.
  unfold modp_entail_wit_2.
  left.
  intros.
  Intros.
  entailer!.
  subst.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  replace (Z.rem (Z.rem (2 ^ i) p_pre * 2) p_pre) with (Z.rem (2 ^ i * 2) p_pre).
  - reflexivity.
  - symmetry. apply Z.mul_rem_idemp_l. lia.
Qed.

Lemma proof_of_modp_return_wit_1 : modp_return_wit_1.
Proof.
  unfold modp_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  unfold problem_49_spec.
  intro Hpre.
  assert (i = n_pre) by lia.
  subst.
  rewrite Z.rem_mod_nonneg by lia.
  reflexivity.
Qed.
