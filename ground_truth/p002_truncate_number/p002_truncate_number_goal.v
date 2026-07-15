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
Require Import p002_truncate_number.
Local Open Scope sac.

(*----- Function truncate_number -----*)

Definition truncate_number_safety_wit_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (0 <= numerator_pre)) (PreH2 : (numerator_pre < INT_MAX)) (PreH3 : (0 < denominator_pre)) (PreH4 : (denominator_pre < INT_MAX)) (PreH5 : (problem_2_pre_z numerator_pre denominator_pre )) ,
  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ” 
  &&  “ (denominator_pre <> 0) ”
.

Definition truncate_number_return_wit_1 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (0 <= numerator_pre)) (PreH2 : (numerator_pre < INT_MAX)) (PreH3 : (0 < denominator_pre)) (PreH4 : (denominator_pre < INT_MAX)) (PreH5 : (problem_2_pre_z numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_2_spec_z numerator_pre denominator_pre (numerator_pre % ( denominator_pre ) ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (0 <= numerator_pre)) (PreH2 : (numerator_pre < INT_MAX)) (PreH3 : (0 < denominator_pre)) (PreH4 : (denominator_pre < INT_MAX)) (PreH5 : (problem_2_pre_z numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_2_spec_z numerator_pre denominator_pre (numerator_pre % ( denominator_pre ) ) ) ”
  &&  emp
).

Definition truncate_number_return_wit_1_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (0 <= numerator_pre)) (PreH2 : (numerator_pre < INT_MAX)) (PreH3 : (0 < denominator_pre)) (PreH4 : (denominator_pre < INT_MAX)) (PreH5 : (problem_2_pre_z numerator_pre denominator_pre )) ,
  (problem_2_spec_z numerator_pre denominator_pre (numerator_pre % ( denominator_pre ) ) )
.

Module Type VC_Correct.


Axiom proof_of_truncate_number_safety_wit_1 : truncate_number_safety_wit_1.
Axiom proof_of_truncate_number_return_wit_1 : truncate_number_return_wit_1.

End VC_Correct.
