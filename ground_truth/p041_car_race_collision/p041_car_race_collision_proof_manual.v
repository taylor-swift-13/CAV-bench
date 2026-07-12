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
From SimpleC.EE.CAV.ground_truth_p041_car_race_collision Require Import p041_car_race_collision_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p041_car_race_collision.
Local Open Scope sac.

Lemma proof_of_car_race_collision_safety_wit_1 : car_race_collision_safety_wit_1.
Proof.
  unfold car_race_collision_safety_wit_1.
  left; intros.
  apply _derivable1_andp_intros; apply dump_spatial_left; nia.
Qed.

Lemma proof_of_car_race_collision_return_wit_1 : car_race_collision_return_wit_1.
Proof.
  unfold car_race_collision_return_wit_1.
  left.
  intros.
  Intros.
  entailer!.
  unfold problem_41_spec_z, problem_41_spec.
  rewrite Z2Nat.inj_mul by lia.
  lia.
Qed.
