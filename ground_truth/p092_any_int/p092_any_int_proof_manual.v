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
From SimpleC.EE.CAV.ground_truth_p092_any_int Require Import p092_any_int_goal.
From SimpleC.EE.CAV.ground_truth_p092_any_int Require Import p092_any_int_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p092_any_int.
Local Open Scope sac.

Ltac solve_any_int :=
  intros; Intros; entailer!;
  unfold problem_92_spec_z, problem_92_math_z, problem_92_pre_z in *;
  intuition lia.

Lemma proof_of_any_int_safety_wit_7 : any_int_safety_wit_7.
Proof. unfold any_int_safety_wit_7; left; solve_any_int. Qed.

Lemma proof_of_any_int_safety_wit_8 : any_int_safety_wit_8.
Proof. unfold any_int_safety_wit_8; left; solve_any_int. Qed.

Lemma proof_of_any_int_safety_wit_9 : any_int_safety_wit_9.
Proof. unfold any_int_safety_wit_9; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_1 : any_int_return_wit_1.
Proof. unfold any_int_return_wit_1; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_2 : any_int_return_wit_2.
Proof. unfold any_int_return_wit_2; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_3 : any_int_return_wit_3.
Proof. unfold any_int_return_wit_3; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_4 : any_int_return_wit_4.
Proof. unfold any_int_return_wit_4; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_5 : any_int_return_wit_5.
Proof. unfold any_int_return_wit_5; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_6 : any_int_return_wit_6.
Proof. unfold any_int_return_wit_6; left; solve_any_int. Qed.

Lemma proof_of_any_int_return_wit_7 : any_int_return_wit_7.
Proof. unfold any_int_return_wit_7; left; solve_any_int. Qed.
