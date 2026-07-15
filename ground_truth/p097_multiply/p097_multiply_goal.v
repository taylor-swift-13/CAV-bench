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
Require Import p097_multiply.
Local Open Scope sac.

(*----- Function abs -----*)

Definition abs_safety_wit_1 := 
forall (x_pre: Z) (PreH1 : (INT_MIN < x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition abs_safety_wit_2 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (x_pre <> (INT_MIN)) ”
.

Definition abs_return_wit_1 := 
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (x_pre = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_1_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre >= 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  (x_pre = (Zabs (x_pre)))
.

Definition abs_return_wit_2 := 
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((-x_pre) = (Zabs (x_pre))) ”
  &&  emp
).

Definition abs_return_wit_2_split_goal_1 := 
forall (x_pre: Z) (PreH1 : (x_pre < 0)) (PreH2 : (INT_MIN < x_pre)) (PreH3 : (x_pre <= INT_MAX)) ,
  ((-x_pre) = (Zabs (x_pre)))
.

(*----- Function multiply -----*)

Definition multiply_safety_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) )) ”
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) )) ”
).

Definition multiply_safety_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) <= INT_MAX) ”
.

Definition multiply_safety_wit_1_split_goal_2 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((INT_MIN) <= ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) )) ”
.

Definition multiply_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (retval = (Zabs (b_pre)))) (PreH2 : (retval_2 = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition multiply_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition multiply_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition multiply_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition multiply_return_wit_1 := 
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_97_spec a_pre b_pre ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) ) ”
  &&  emp
) \/
(
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (problem_97_spec a_pre b_pre ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) ) ”
  &&  emp
).

Definition multiply_return_wit_1_split_goal_1 := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (Zabs (b_pre)))) (PreH2 : (retval = (Zabs (a_pre)))) (PreH3 : (INT_MIN < a_pre)) (PreH4 : (a_pre <= INT_MAX)) (PreH5 : (INT_MIN < b_pre)) (PreH6 : (b_pre <= INT_MAX)) ,
  (problem_97_spec a_pre b_pre ((retval % ( 10 ) ) * (retval_2 % ( 10 ) ) ) )
.

Definition multiply_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ”
.

Definition multiply_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (PreH1 : (INT_MIN < a_pre)) (PreH2 : (a_pre <= INT_MAX)) (PreH3 : (INT_MIN < b_pre)) (PreH4 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  emp
.

Definition multiply_partial_solve_wit_1 := multiply_partial_solve_wit_1_pure -> multiply_partial_solve_wit_1_aux.

Definition multiply_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  ((( &( "b" ) )) # Int  |-> b_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
.

Definition multiply_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (retval: Z) (PreH1 : (retval = (Zabs (a_pre)))) (PreH2 : (INT_MIN < a_pre)) (PreH3 : (a_pre <= INT_MAX)) (PreH4 : (INT_MIN < b_pre)) (PreH5 : (b_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ” 
  &&  “ (retval = (Zabs (a_pre))) ” 
  &&  “ (INT_MIN < a_pre) ” 
  &&  “ (a_pre <= INT_MAX) ” 
  &&  “ (INT_MIN < b_pre) ” 
  &&  “ (b_pre <= INT_MAX) ”
  &&  emp
.

Definition multiply_partial_solve_wit_2 := multiply_partial_solve_wit_2_pure -> multiply_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_abs_safety_wit_1 : abs_safety_wit_1.
Axiom proof_of_abs_safety_wit_2 : abs_safety_wit_2.
Axiom proof_of_abs_return_wit_1 : abs_return_wit_1.
Axiom proof_of_abs_return_wit_2 : abs_return_wit_2.
Axiom proof_of_multiply_safety_wit_1 : multiply_safety_wit_1.
Axiom proof_of_multiply_safety_wit_2 : multiply_safety_wit_2.
Axiom proof_of_multiply_safety_wit_3 : multiply_safety_wit_3.
Axiom proof_of_multiply_safety_wit_4 : multiply_safety_wit_4.
Axiom proof_of_multiply_safety_wit_5 : multiply_safety_wit_5.
Axiom proof_of_multiply_return_wit_1 : multiply_return_wit_1.
Axiom proof_of_multiply_partial_solve_wit_1_pure : multiply_partial_solve_wit_1_pure.
Axiom proof_of_multiply_partial_solve_wit_1 : multiply_partial_solve_wit_1.
Axiom proof_of_multiply_partial_solve_wit_2_pure : multiply_partial_solve_wit_2_pure.
Axiom proof_of_multiply_partial_solve_wit_2 : multiply_partial_solve_wit_2.

End VC_Correct.
