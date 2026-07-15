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
Require Import p151_double_the_difference.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function double_the_difference -----*)

Definition double_the_difference_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = lst_size_pre)) (PreH4 : (problem_151_pre_z input )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_the_difference_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = lst_size_pre)) (PreH4 : (problem_151_pre_z input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_the_difference_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : ((Zlength (input)) = lst_size_pre)) (PreH8 : (problem_151_pre_z input )) (PreH9 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_the_difference_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input 0) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition double_the_difference_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition double_the_difference_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition double_the_difference_safety_wit_7 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((Znth i input 0) * (Znth i input 0) ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((Znth i input 0) * (Znth i input 0) ) )) ”
).

Definition double_the_difference_safety_wit_7_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX) ”
.

Definition double_the_difference_safety_wit_7_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + ((Znth i input 0) * (Znth i input 0) ) )) ”
.

Definition double_the_difference_safety_wit_8 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input 0) * (Znth i input 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input 0) * (Znth i input 0) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input 0) * (Znth i input 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input 0) * (Znth i input 0) )) ”
).

Definition double_the_difference_safety_wit_8_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input 0) * (Znth i input 0) ) <= INT_MAX) ”
.

Definition double_the_difference_safety_wit_8_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "x" ) )) # Int  |-> (Znth i input 0))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= ((Znth i input 0) * (Znth i input 0) )) ”
.

Definition double_the_difference_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + ((Znth i input 0) * (Znth i input 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition double_the_difference_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition double_the_difference_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition double_the_difference_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = lst_size_pre)) (PreH4 : (problem_151_pre_z input )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = lst_size_pre) ” 
  &&  “ (problem_151_pre_z input ) ” 
  &&  “ (problem_151_prefix_z input 0 0 ) ”
  &&  (IntArray.full lst_pre lst_size_pre input )
) \/
(
forall (lst_size_pre: Z) (input: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = lst_size_pre)) (PreH4 : (problem_151_pre_z input )) ,
  TT && emp 
|--
  “ (problem_151_prefix_z input 0 0 ) ”
  &&  emp
).

Definition double_the_difference_entail_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input: (@list Z)) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = lst_size_pre)) (PreH4 : (problem_151_pre_z input )) ,
  (problem_151_prefix_z input 0 0 )
.

Definition double_the_difference_entail_wit_2_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (0 <= (sum + ((Znth i input 0) * (Znth i input 0) ) )) ” 
  &&  “ ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = lst_size_pre) ” 
  &&  “ (problem_151_pre_z input ) ” 
  &&  “ (problem_151_prefix_z input (i + 1 ) (sum + ((Znth i input 0) * (Znth i input 0) ) ) ) ”
  &&  (IntArray.full lst_pre lst_size_pre input )
) \/
(
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  TT && emp 
|--
  “ (problem_151_prefix_z input (i + 1 ) (sum + ((Znth i input 0) * (Znth i input 0) ) ) ) ” 
  &&  “ ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX) ”
  &&  emp
).

Definition double_the_difference_entail_wit_2_1_split_goal_1 := 
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (problem_151_prefix_z input (i + 1 ) (sum + ((Znth i input 0) * (Znth i input 0) ) ) )
.

Definition double_the_difference_entail_wit_2_1_split_goal_2 := 
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) <> 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  ((sum + ((Znth i input 0) * (Znth i input 0) ) ) <= INT_MAX)
.

Definition double_the_difference_entail_wit_2_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = lst_size_pre) ” 
  &&  “ (problem_151_pre_z input ) ” 
  &&  “ (problem_151_prefix_z input (i + 1 ) sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input )
) \/
(
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  TT && emp 
|--
  “ (problem_151_prefix_z input (i + 1 ) sum ) ”
  &&  emp
).

Definition double_the_difference_entail_wit_2_2_split_goal_1 := 
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (lst_size_pre < INT_MAX)) (PreH6 : (0 <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : ((Zlength (input)) = lst_size_pre)) (PreH9 : (problem_151_pre_z input )) (PreH10 : (problem_151_prefix_z input i sum )) ,
  (problem_151_prefix_z input (i + 1 ) sum )
.

Definition double_the_difference_entail_wit_2_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = lst_size_pre) ” 
  &&  “ (problem_151_pre_z input ) ” 
  &&  “ (problem_151_prefix_z input (i + 1 ) sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input )
) \/
(
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  TT && emp 
|--
  “ (problem_151_prefix_z input (i + 1 ) sum ) ”
  &&  emp
).

Definition double_the_difference_entail_wit_2_3_split_goal_1 := 
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i input 0) % ( 2 ) ) = 0)) (PreH2 : ((Znth i input 0) > 0)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= i)) (PreH5 : (i <= lst_size_pre)) (PreH6 : (lst_size_pre < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : ((Zlength (input)) = lst_size_pre)) (PreH10 : (problem_151_pre_z input )) (PreH11 : (problem_151_prefix_z input i sum )) ,
  (problem_151_prefix_z input (i + 1 ) sum )
.

Definition double_the_difference_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : ((Zlength (input)) = lst_size_pre)) (PreH8 : (problem_151_pre_z input )) (PreH9 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (problem_151_spec_z input sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input )
) \/
(
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : ((Zlength (input)) = lst_size_pre)) (PreH8 : (problem_151_pre_z input )) (PreH9 : (problem_151_prefix_z input i sum )) ,
  TT && emp 
|--
  “ (problem_151_spec_z input sum ) ”
  &&  emp
).

Definition double_the_difference_return_wit_1_split_goal_1 := 
forall (lst_size_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : ((Zlength (input)) = lst_size_pre)) (PreH8 : (problem_151_pre_z input )) (PreH9 : (problem_151_prefix_z input i sum )) ,
  (problem_151_spec_z input sum )
.

Definition double_the_difference_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (lst_size_pre < INT_MAX)) (PreH5 : (0 <= sum)) (PreH6 : (sum <= INT_MAX)) (PreH7 : ((Zlength (input)) = lst_size_pre)) (PreH8 : (problem_151_pre_z input )) (PreH9 : (problem_151_prefix_z input i sum )) ,
  (IntArray.full lst_pre lst_size_pre input )
|--
  “ (i < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((Zlength (input)) = lst_size_pre) ” 
  &&  “ (problem_151_pre_z input ) ” 
  &&  “ (problem_151_prefix_z input i sum ) ”
  &&  (((lst_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_double_the_difference_safety_wit_1 : double_the_difference_safety_wit_1.
Axiom proof_of_double_the_difference_safety_wit_2 : double_the_difference_safety_wit_2.
Axiom proof_of_double_the_difference_safety_wit_3 : double_the_difference_safety_wit_3.
Axiom proof_of_double_the_difference_safety_wit_4 : double_the_difference_safety_wit_4.
Axiom proof_of_double_the_difference_safety_wit_5 : double_the_difference_safety_wit_5.
Axiom proof_of_double_the_difference_safety_wit_6 : double_the_difference_safety_wit_6.
Axiom proof_of_double_the_difference_safety_wit_7 : double_the_difference_safety_wit_7.
Axiom proof_of_double_the_difference_safety_wit_8 : double_the_difference_safety_wit_8.
Axiom proof_of_double_the_difference_safety_wit_9 : double_the_difference_safety_wit_9.
Axiom proof_of_double_the_difference_safety_wit_10 : double_the_difference_safety_wit_10.
Axiom proof_of_double_the_difference_safety_wit_11 : double_the_difference_safety_wit_11.
Axiom proof_of_double_the_difference_entail_wit_1 : double_the_difference_entail_wit_1.
Axiom proof_of_double_the_difference_entail_wit_2_1 : double_the_difference_entail_wit_2_1.
Axiom proof_of_double_the_difference_entail_wit_2_2 : double_the_difference_entail_wit_2_2.
Axiom proof_of_double_the_difference_entail_wit_2_3 : double_the_difference_entail_wit_2_3.
Axiom proof_of_double_the_difference_return_wit_1 : double_the_difference_return_wit_1.
Axiom proof_of_double_the_difference_partial_solve_wit_1 : double_the_difference_partial_solve_wit_1.

End VC_Correct.
