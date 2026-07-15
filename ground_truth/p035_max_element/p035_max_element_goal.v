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
Require Import p035_max_element.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function max_element -----*)

Definition max_element_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  ((( &( "current" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre xs )
|--
  “ (0 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 0) ”
.

Definition max_element_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.full l_pre l_size_pre xs )
  **  ((( &( "current" ) )) # Int  |-> (Znth 0 xs 0))
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition max_element_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current < (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> (Znth i xs 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_element_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current >= (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "current" ) )) # Int  |-> current)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition max_element_entail_wit_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ” 
  &&  “ (problem_35_prefix xs 1 (Znth 0 xs 0) ) ”
  &&  (IntArray.full l_pre l_size_pre xs )
) \/
(
forall (l_size_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  TT && emp 
|--
  “ (problem_35_prefix xs 1 (Znth 0 xs 0) ) ”
  &&  emp
).

Definition max_element_entail_wit_1_split_goal_1 := 
forall (l_size_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  (problem_35_prefix xs 1 (Znth 0 xs 0) )
.

Definition max_element_entail_wit_2_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current < (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ” 
  &&  “ (problem_35_prefix xs (i + 1 ) (Znth i xs 0) ) ”
  &&  (IntArray.full l_pre l_size_pre xs )
) \/
(
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current < (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  TT && emp 
|--
  “ (problem_35_prefix xs (i + 1 ) (Znth i xs 0) ) ”
  &&  emp
).

Definition max_element_entail_wit_2_1_split_goal_1 := 
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current < (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (problem_35_prefix xs (i + 1 ) (Znth i xs 0) )
.

Definition max_element_entail_wit_2_2 := 
(
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current >= (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ” 
  &&  “ (problem_35_prefix xs (i + 1 ) current ) ”
  &&  (IntArray.full l_pre l_size_pre xs )
) \/
(
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current >= (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  TT && emp 
|--
  “ (problem_35_prefix xs (i + 1 ) current ) ”
  &&  emp
).

Definition max_element_entail_wit_2_2_split_goal_1 := 
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current >= (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (problem_35_prefix xs (i + 1 ) current )
.

Definition max_element_return_wit_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (i >= l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (xs)) = l_size_pre)) (PreH6 : (problem_35_pre xs )) (PreH7 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (problem_35_spec xs current ) ”
  &&  (IntArray.full l_pre l_size_pre xs )
) \/
(
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (i >= l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (xs)) = l_size_pre)) (PreH6 : (problem_35_pre xs )) (PreH7 : (problem_35_prefix xs i current )) ,
  TT && emp 
|--
  “ (problem_35_spec xs current ) ”
  &&  emp
).

Definition max_element_return_wit_1_split_goal_1 := 
forall (l_size_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (i >= l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (xs)) = l_size_pre)) (PreH6 : (problem_35_pre xs )) (PreH7 : (problem_35_prefix xs i current )) ,
  (problem_35_spec xs current )
.

Definition max_element_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (PreH1 : (0 < l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (xs)) = l_size_pre)) (PreH4 : (problem_35_pre xs )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (0 < l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ”
  &&  (((l_pre + (0 * sizeof(INT)))) # Int  |-> (Znth 0 xs 0))
  **  (IntArray.missing_i l_pre 0 0 l_size_pre xs )
.

Definition max_element_partial_solve_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (xs)) = l_size_pre)) (PreH6 : (problem_35_pre xs )) (PreH7 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ” 
  &&  “ (problem_35_prefix xs i current ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre xs )
.

Definition max_element_partial_solve_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (xs: (@list Z)) (current: Z) (i: Z) (PreH1 : (current < (Znth i xs 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (xs)) = l_size_pre)) (PreH7 : (problem_35_pre xs )) (PreH8 : (problem_35_prefix xs i current )) ,
  (IntArray.full l_pre l_size_pre xs )
|--
  “ (current < (Znth i xs 0)) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (xs)) = l_size_pre) ” 
  &&  “ (problem_35_pre xs ) ” 
  &&  “ (problem_35_prefix xs i current ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i xs 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre xs )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_max_element_safety_wit_1 : max_element_safety_wit_1.
Axiom proof_of_max_element_safety_wit_2 : max_element_safety_wit_2.
Axiom proof_of_max_element_safety_wit_3 : max_element_safety_wit_3.
Axiom proof_of_max_element_safety_wit_4 : max_element_safety_wit_4.
Axiom proof_of_max_element_entail_wit_1 : max_element_entail_wit_1.
Axiom proof_of_max_element_entail_wit_2_1 : max_element_entail_wit_2_1.
Axiom proof_of_max_element_entail_wit_2_2 : max_element_entail_wit_2_2.
Axiom proof_of_max_element_return_wit_1 : max_element_return_wit_1.
Axiom proof_of_max_element_partial_solve_wit_1 : max_element_partial_solve_wit_1.
Axiom proof_of_max_element_partial_solve_wit_2 : max_element_partial_solve_wit_2.
Axiom proof_of_max_element_partial_solve_wit_3 : max_element_partial_solve_wit_3.

End VC_Correct.
