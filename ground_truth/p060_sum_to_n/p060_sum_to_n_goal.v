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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p060_sum_to_n.
Local Open Scope sac.

(*----- Function sum_to_n -----*)

Definition sum_to_n_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((n_pre * (n_pre + 1 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sum_to_n_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre * (n_pre + 1 ) )) ”
.

Definition sum_to_n_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition sum_to_n_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sum_to_n_safety_wit_5 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sum_to_n_return_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  TT && emp 
|--
  “ (problem_60_spec_z n_pre ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  TT && emp 
|--
  “ (problem_60_spec_z n_pre ((n_pre * (n_pre + 1 ) ) ÷ 2 ) ) ”
  &&  emp
).

Definition sum_to_n_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (problem_60_pre_z n_pre )) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 46340)) ,
  (problem_60_spec_z n_pre ((n_pre * (n_pre + 1 ) ) ÷ 2 ) )
.

Module Type VC_Correct.


Axiom proof_of_sum_to_n_safety_wit_1 : sum_to_n_safety_wit_1.
Axiom proof_of_sum_to_n_safety_wit_2 : sum_to_n_safety_wit_2.
Axiom proof_of_sum_to_n_safety_wit_3 : sum_to_n_safety_wit_3.
Axiom proof_of_sum_to_n_safety_wit_4 : sum_to_n_safety_wit_4.
Axiom proof_of_sum_to_n_safety_wit_5 : sum_to_n_safety_wit_5.
Axiom proof_of_sum_to_n_return_wit_1 : sum_to_n_return_wit_1.

End VC_Correct.
