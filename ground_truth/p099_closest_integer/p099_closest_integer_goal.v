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
Require Import p099_closest_integer.
Local Open Scope sac.

(*----- Function closest_integer -----*)

Definition closest_integer_safety_wit_1 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ” 
  &&  “ (denominator_pre <> 0) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ” 
  &&  “ (denominator_pre <> 0) ”
).

Definition closest_integer_safety_wit_1_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ”
.

Definition closest_integer_safety_wit_1_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (denominator_pre <> 0) ”
.

Definition closest_integer_safety_wit_2 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ” 
  &&  “ (denominator_pre <> 0) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ” 
  &&  “ (denominator_pre <> 0) ”
).

Definition closest_integer_safety_wit_2_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((numerator_pre <> (INT_MIN)) \/ (denominator_pre <> (-1))) ”
.

Definition closest_integer_safety_wit_2_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (denominator_pre <> 0) ”
.

Definition closest_integer_safety_wit_3 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition closest_integer_safety_wit_4 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((2 * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * (numerator_pre % ( denominator_pre ) ) )) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((2 * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * (numerator_pre % ( denominator_pre ) ) )) ”
).

Definition closest_integer_safety_wit_4_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((2 * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ”
.

Definition closest_integer_safety_wit_4_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((INT_MIN) <= (2 * (numerator_pre % ( denominator_pre ) ) )) ”
.

Definition closest_integer_safety_wit_5 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition closest_integer_safety_wit_6 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) + 1 )) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) + 1 )) ”
).

Definition closest_integer_safety_wit_6_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) + 1 ) <= INT_MAX) ”
.

Definition closest_integer_safety_wit_6_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) + 1 )) ”
.

Definition closest_integer_safety_wit_7 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition closest_integer_safety_wit_8 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH2 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition closest_integer_safety_wit_9 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((-2) * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-2) * (numerator_pre % ( denominator_pre ) ) )) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((-2) * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((-2) * (numerator_pre % ( denominator_pre ) ) )) ”
).

Definition closest_integer_safety_wit_9_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((-2) * (numerator_pre % ( denominator_pre ) ) ) <= INT_MAX) ”
.

Definition closest_integer_safety_wit_9_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((INT_MIN) <= ((-2) * (numerator_pre % ( denominator_pre ) ) )) ”
.

Definition closest_integer_safety_wit_10 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (2 <> (INT_MIN)) ”
.

Definition closest_integer_safety_wit_11 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition closest_integer_safety_wit_12 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) - 1 )) ”
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) - 1 )) ”
).

Definition closest_integer_safety_wit_12_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (((numerator_pre ÷ denominator_pre ) - 1 ) <= INT_MAX) ”
.

Definition closest_integer_safety_wit_12_split_goal_2 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ ((INT_MIN) <= ((numerator_pre ÷ denominator_pre ) - 1 )) ”
.

Definition closest_integer_safety_wit_13 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  ((( &( "r" ) )) # Int  |-> (numerator_pre % ( denominator_pre ) ))
  **  ((( &( "q" ) )) # Int  |-> (numerator_pre ÷ denominator_pre ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition closest_integer_return_wit_1 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) >= 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) >= 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
).

Definition closest_integer_return_wit_1_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((numerator_pre % ( denominator_pre ) ) >= 0)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) )
.

Definition closest_integer_return_wit_2 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
).

Definition closest_integer_return_wit_2_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) )
.

Definition closest_integer_return_wit_3 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) - 1 ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) - 1 ) ) ”
  &&  emp
).

Definition closest_integer_return_wit_3_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : (((-2) * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) < 0)) (PreH3 : ((numerator_pre % ( denominator_pre ) ) <= 0)) (PreH4 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) - 1 ) )
.

Definition closest_integer_return_wit_4 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) ) ”
  &&  emp
).

Definition closest_integer_return_wit_4_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) < denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  (problem_99_spec_ratio numerator_pre denominator_pre (numerator_pre ÷ denominator_pre ) )
.

Definition closest_integer_return_wit_5 := 
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) + 1 ) ) ”
  &&  emp
) \/
(
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  TT && emp 
|--
  “ (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) + 1 ) ) ”
  &&  emp
).

Definition closest_integer_return_wit_5_split_goal_1 := 
forall (denominator_pre: Z) (numerator_pre: Z) (PreH1 : ((2 * (numerator_pre % ( denominator_pre ) ) ) >= denominator_pre)) (PreH2 : ((numerator_pre % ( denominator_pre ) ) > 0)) (PreH3 : (problem_99_pre_ratio numerator_pre denominator_pre )) ,
  (problem_99_spec_ratio numerator_pre denominator_pre ((numerator_pre ÷ denominator_pre ) + 1 ) )
.

Module Type VC_Correct.


Axiom proof_of_closest_integer_safety_wit_1 : closest_integer_safety_wit_1.
Axiom proof_of_closest_integer_safety_wit_2 : closest_integer_safety_wit_2.
Axiom proof_of_closest_integer_safety_wit_3 : closest_integer_safety_wit_3.
Axiom proof_of_closest_integer_safety_wit_4 : closest_integer_safety_wit_4.
Axiom proof_of_closest_integer_safety_wit_5 : closest_integer_safety_wit_5.
Axiom proof_of_closest_integer_safety_wit_6 : closest_integer_safety_wit_6.
Axiom proof_of_closest_integer_safety_wit_7 : closest_integer_safety_wit_7.
Axiom proof_of_closest_integer_safety_wit_8 : closest_integer_safety_wit_8.
Axiom proof_of_closest_integer_safety_wit_9 : closest_integer_safety_wit_9.
Axiom proof_of_closest_integer_safety_wit_10 : closest_integer_safety_wit_10.
Axiom proof_of_closest_integer_safety_wit_11 : closest_integer_safety_wit_11.
Axiom proof_of_closest_integer_safety_wit_12 : closest_integer_safety_wit_12.
Axiom proof_of_closest_integer_safety_wit_13 : closest_integer_safety_wit_13.
Axiom proof_of_closest_integer_return_wit_1 : closest_integer_return_wit_1.
Axiom proof_of_closest_integer_return_wit_2 : closest_integer_return_wit_2.
Axiom proof_of_closest_integer_return_wit_3 : closest_integer_return_wit_3.
Axiom proof_of_closest_integer_return_wit_4 : closest_integer_return_wit_4.
Axiom proof_of_closest_integer_return_wit_5 : closest_integer_return_wit_5.

End VC_Correct.
