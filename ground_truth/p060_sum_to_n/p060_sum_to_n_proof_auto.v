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
From SimpleC.EE.CAV.ground_truth_p060_sum_to_n Require Import p060_sum_to_n_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p060_sum_to_n.
Local Open Scope sac.

Lemma proof_of_sum_to_n_safety_wit_1 : sum_to_n_safety_wit_1.
Proof. Admitted. 

Lemma proof_of_sum_to_n_safety_wit_2 : sum_to_n_safety_wit_2.
Proof. Admitted. 

Lemma proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Proof. Admitted. 

Lemma proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Proof. Admitted. 

Lemma proof_of_sum_to_n_safety_wit_5 : sum_to_n_safety_wit_5.
Proof. Admitted. 

