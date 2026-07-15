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
From SimpleC.EE.CAV.ground_truth_p071_triangle_area Require Import p071_triangle_area_goal.
From SimpleC.EE.CAV.ground_truth_p071_triangle_area Require Import p071_triangle_area_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p071_triangle_area.
Local Open Scope sac.

Ltac solve_safety_71 name :=
  unfold name; left; intros;
  Intros; entailer!;
  unfold problem_71_pre_z, heron_radicand_71_z in *; tauto.

Lemma proof_of_triangle_area_safety_wit_10 : triangle_area_safety_wit_10.
Proof. solve_safety_71 triangle_area_safety_wit_10. Qed.

Lemma proof_of_triangle_area_safety_wit_11 : triangle_area_safety_wit_11.
Proof. solve_safety_71 triangle_area_safety_wit_11. Qed.

Lemma proof_of_triangle_area_safety_wit_12 : triangle_area_safety_wit_12.
Proof. solve_safety_71 triangle_area_safety_wit_12. Qed.

Lemma proof_of_triangle_area_safety_wit_19 : triangle_area_safety_wit_19.
Proof. solve_safety_71 triangle_area_safety_wit_19. Qed.

Lemma proof_of_triangle_area_safety_wit_20 : triangle_area_safety_wit_20.
Proof. solve_safety_71 triangle_area_safety_wit_20. Qed.

Lemma proof_of_triangle_area_safety_wit_28 : triangle_area_safety_wit_28.
Proof. solve_safety_71 triangle_area_safety_wit_28. Qed.

Lemma proof_of_triangle_area_safety_wit_29 : triangle_area_safety_wit_29.
Proof. solve_safety_71 triangle_area_safety_wit_29. Qed.

Lemma proof_of_triangle_area_safety_wit_30 : triangle_area_safety_wit_30.
Proof. solve_safety_71 triangle_area_safety_wit_30. Qed.

Ltac begin_return_71 name :=
  unfold name; left; intros; Intros; entailer!;
  unfold problem_71_spec_z, valid_triangle_71_z,
         heron_radicand_71_z in *.

Lemma proof_of_triangle_area_return_wit_1 : triangle_area_return_wit_1.
Proof.
  begin_return_71 triangle_area_return_wit_1.
  clear PreH7. left. split; [repeat split; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_2 : triangle_area_return_wit_2.
Proof.
  begin_return_71 triangle_area_return_wit_2.
  clear PreH6. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_3 : triangle_area_return_wit_3.
Proof.
  begin_return_71 triangle_area_return_wit_3.
  clear PreH5. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_4 : triangle_area_return_wit_4.
Proof.
  begin_return_71 triangle_area_return_wit_4.
  clear PreH7. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_5 : triangle_area_return_wit_5.
Proof.
  begin_return_71 triangle_area_return_wit_5.
  clear PreH3. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_6 : triangle_area_return_wit_6.
Proof.
  begin_return_71 triangle_area_return_wit_6.
  clear PreH2. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.

Lemma proof_of_triangle_area_return_wit_7 : triangle_area_return_wit_7.
Proof.
  begin_return_71 triangle_area_return_wit_7.
  clear PreH4. right. split;
    [intros [? [? [? [? [? ?]]]]]; lia | reflexivity].
Qed.
