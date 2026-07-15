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
Require Import p133_sum_squares.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function sum_squares -----*)

Definition sum_squares_safety_wit_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre < INT_MAX)) (PreH3 : ((Zlength (nums)) = size_pre)) (PreH4 : ((Zlength (dens)) = size_pre)) (PreH5 : (problem_133_pre_z nums dens )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre < INT_MAX)) (PreH3 : ((Zlength (nums)) = size_pre)) (PreH4 : ((Zlength (dens)) = size_pre)) (PreH5 : (problem_133_pre_z nums dens )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_3 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ” 
  &&  “ ((Znth i dens 0) <> 0) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ” 
  &&  “ ((Znth i dens 0) <> 0) ”
).

Definition sum_squares_safety_wit_3_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ”
.

Definition sum_squares_safety_wit_3_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "q" ) )) # Int  |->_)
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((Znth i dens 0) <> 0) ”
.

Definition sum_squares_safety_wit_4 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ” 
  &&  “ ((Znth i dens 0) <> 0) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ” 
  &&  “ ((Znth i dens 0) <> 0) ”
).

Definition sum_squares_safety_wit_4_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i nums 0) <> (INT_MIN)) \/ ((Znth i dens 0) <> (-1))) ”
.

Definition sum_squares_safety_wit_4_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((Znth i dens 0) <> 0) ”
.

Definition sum_squares_safety_wit_5 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sum_squares_safety_wit_6 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 )) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 )) ”
).

Definition sum_squares_safety_wit_6_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_6_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 )) ”
.

Definition sum_squares_safety_wit_7 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sum_squares_safety_wit_8 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) )) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) )) ”
).

Definition sum_squares_safety_wit_8_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_8_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) )) ”
.

Definition sum_squares_safety_wit_9 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) )) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) )) ”
).

Definition sum_squares_safety_wit_9_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_9_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) )) ”
.

Definition sum_squares_safety_wit_10 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) )) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) )) ”
).

Definition sum_squares_safety_wit_10_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_10_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) )) ”
.

Definition sum_squares_safety_wit_11 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) )) ”
) \/
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) )) ”
).

Definition sum_squares_safety_wit_11_split_goal_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) <= INT_MAX) ”
.

Definition sum_squares_safety_wit_11_split_goal_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  ((( &( "z" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "r" ) )) # Int  |-> ((Znth i nums 0) % ( (Znth i dens 0) ) ))
  **  ((( &( "q" ) )) # Int  |-> ((Znth i nums 0) ÷ (Znth i dens 0) ))
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((INT_MIN) <= (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) )) ”
.

Definition sum_squares_safety_wit_12 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sum_squares_safety_wit_13 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
  **  ((( &( "numerators" ) )) # Ptr  |-> numerators_pre)
  **  ((( &( "denominators" ) )) # Ptr  |-> denominators_pre)
  **  ((( &( "size" ) )) # Int  |-> size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sum_squares_entail_wit_1 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre < INT_MAX)) (PreH3 : ((Zlength (nums)) = size_pre)) (PreH4 : ((Zlength (dens)) = size_pre)) (PreH5 : (problem_133_pre_z nums dens )) ,
  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens 0 0 ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
) \/
(
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre < INT_MAX)) (PreH3 : ((Zlength (nums)) = size_pre)) (PreH4 : ((Zlength (dens)) = size_pre)) (PreH5 : (problem_133_pre_z nums dens )) ,
  TT && emp 
|--
  “ (problem_133_prefix_z nums dens 0 0 ) ”
  &&  emp
).

Definition sum_squares_entail_wit_1_split_goal_1 := 
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre < INT_MAX)) (PreH3 : ((Zlength (nums)) = size_pre)) (PreH4 : ((Zlength (dens)) = size_pre)) (PreH5 : (problem_133_pre_z nums dens )) ,
  (problem_133_prefix_z nums dens 0 0 )
.

Definition sum_squares_entail_wit_2_1 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens (i + 1 ) (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
) \/
(
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  TT && emp 
|--
  “ (problem_133_prefix_z nums dens (i + 1 ) (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) ) ”
  &&  emp
).

Definition sum_squares_entail_wit_2_1_split_goal_1 := 
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) > 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (problem_133_prefix_z nums dens (i + 1 ) (sum + ((((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) * (((Znth i nums 0) ÷ (Znth i dens 0) ) + 1 ) ) ) )
.

Definition sum_squares_entail_wit_2_2 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens (i + 1 ) (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
) \/
(
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  TT && emp 
|--
  “ (problem_133_prefix_z nums dens (i + 1 ) (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) ) ”
  &&  emp
).

Definition sum_squares_entail_wit_2_2_split_goal_1 := 
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (((Znth i nums 0) % ( (Znth i dens 0) ) ) <= 0)) (PreH2 : (i < size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= size_pre)) (PreH5 : (size_pre < INT_MAX)) (PreH6 : ((Zlength (nums)) = size_pre)) (PreH7 : ((Zlength (dens)) = size_pre)) (PreH8 : (problem_133_pre_z nums dens )) (PreH9 : (problem_133_prefix_z nums dens i sum )) (PreH10 : (0 <= size_pre)) (PreH11 : (size_pre < INT_MAX)) (PreH12 : ((Zlength (nums)) = size_pre)) (PreH13 : ((Zlength (dens)) = size_pre)) (PreH14 : (problem_133_pre_z nums dens )) ,
  (problem_133_prefix_z nums dens (i + 1 ) (sum + (((Znth i nums 0) ÷ (Znth i dens 0) ) * ((Znth i nums 0) ÷ (Znth i dens 0) ) ) ) )
.

Definition sum_squares_return_wit_1 := 
(
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (problem_133_spec_z nums dens sum ) ”
  &&  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
) \/
(
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  TT && emp 
|--
  “ (problem_133_spec_z nums dens sum ) ”
  &&  emp
).

Definition sum_squares_return_wit_1_split_goal_1 := 
forall (size_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i >= size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (problem_133_spec_z nums dens sum )
.

Definition sum_squares_partial_solve_wit_1 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (i < size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens i sum ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (((numerators_pre + (i * sizeof(INT)))) # Int  |-> (Znth i nums 0))
  **  (IntArray.missing_i numerators_pre i 0 size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
.

Definition sum_squares_partial_solve_wit_2 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (i < size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens i sum ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (((denominators_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dens 0))
  **  (IntArray.missing_i denominators_pre i 0 size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
.

Definition sum_squares_partial_solve_wit_3 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full denominators_pre size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
|--
  “ (i < size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens i sum ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (((numerators_pre + (i * sizeof(INT)))) # Int  |-> (Znth i nums 0))
  **  (IntArray.missing_i numerators_pre i 0 size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
.

Definition sum_squares_partial_solve_wit_4 := 
forall (size_pre: Z) (denominators_pre: Z) (numerators_pre: Z) (dens: (@list Z)) (nums: (@list Z)) (sum: Z) (i: Z) (PreH1 : (i < size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= size_pre)) (PreH4 : (size_pre < INT_MAX)) (PreH5 : ((Zlength (nums)) = size_pre)) (PreH6 : ((Zlength (dens)) = size_pre)) (PreH7 : (problem_133_pre_z nums dens )) (PreH8 : (problem_133_prefix_z nums dens i sum )) (PreH9 : (0 <= size_pre)) (PreH10 : (size_pre < INT_MAX)) (PreH11 : ((Zlength (nums)) = size_pre)) (PreH12 : ((Zlength (dens)) = size_pre)) (PreH13 : (problem_133_pre_z nums dens )) ,
  (IntArray.full numerators_pre size_pre nums )
  **  (IntArray.full denominators_pre size_pre dens )
|--
  “ (i < size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ” 
  &&  “ (problem_133_prefix_z nums dens i sum ) ” 
  &&  “ (0 <= size_pre) ” 
  &&  “ (size_pre < INT_MAX) ” 
  &&  “ ((Zlength (nums)) = size_pre) ” 
  &&  “ ((Zlength (dens)) = size_pre) ” 
  &&  “ (problem_133_pre_z nums dens ) ”
  &&  (((denominators_pre + (i * sizeof(INT)))) # Int  |-> (Znth i dens 0))
  **  (IntArray.missing_i denominators_pre i 0 size_pre dens )
  **  (IntArray.full numerators_pre size_pre nums )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_sum_squares_safety_wit_1 : sum_squares_safety_wit_1.
Axiom proof_of_sum_squares_safety_wit_2 : sum_squares_safety_wit_2.
Axiom proof_of_sum_squares_safety_wit_3 : sum_squares_safety_wit_3.
Axiom proof_of_sum_squares_safety_wit_4 : sum_squares_safety_wit_4.
Axiom proof_of_sum_squares_safety_wit_5 : sum_squares_safety_wit_5.
Axiom proof_of_sum_squares_safety_wit_6 : sum_squares_safety_wit_6.
Axiom proof_of_sum_squares_safety_wit_7 : sum_squares_safety_wit_7.
Axiom proof_of_sum_squares_safety_wit_8 : sum_squares_safety_wit_8.
Axiom proof_of_sum_squares_safety_wit_9 : sum_squares_safety_wit_9.
Axiom proof_of_sum_squares_safety_wit_10 : sum_squares_safety_wit_10.
Axiom proof_of_sum_squares_safety_wit_11 : sum_squares_safety_wit_11.
Axiom proof_of_sum_squares_safety_wit_12 : sum_squares_safety_wit_12.
Axiom proof_of_sum_squares_safety_wit_13 : sum_squares_safety_wit_13.
Axiom proof_of_sum_squares_entail_wit_1 : sum_squares_entail_wit_1.
Axiom proof_of_sum_squares_entail_wit_2_1 : sum_squares_entail_wit_2_1.
Axiom proof_of_sum_squares_entail_wit_2_2 : sum_squares_entail_wit_2_2.
Axiom proof_of_sum_squares_return_wit_1 : sum_squares_return_wit_1.
Axiom proof_of_sum_squares_partial_solve_wit_1 : sum_squares_partial_solve_wit_1.
Axiom proof_of_sum_squares_partial_solve_wit_2 : sum_squares_partial_solve_wit_2.
Axiom proof_of_sum_squares_partial_solve_wit_3 : sum_squares_partial_solve_wit_3.
Axiom proof_of_sum_squares_partial_solve_wit_4 : sum_squares_partial_solve_wit_4.

End VC_Correct.
