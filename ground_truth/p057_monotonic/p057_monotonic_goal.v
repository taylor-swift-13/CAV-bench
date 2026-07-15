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
Require Import p057_monotonic.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function monotonic -----*)

Definition monotonic_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  ((( &( "incr" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  ((( &( "decr" ) )) # Int  |->_)
  **  ((( &( "incr" ) )) # Int  |-> 1)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "decr" ) )) # Int  |-> 1)
  **  ((( &( "incr" ) )) # Int  |-> 1)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_57_pre_z input )) (PreH7 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition monotonic_safety_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_57_pre_z input )) (PreH7 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition monotonic_safety_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition monotonic_safety_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> 0)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition monotonic_safety_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_10 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_11 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition monotonic_safety_wit_12 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition monotonic_safety_wit_13 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> 0)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition monotonic_safety_wit_14 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition monotonic_safety_wit_15 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition monotonic_safety_wit_16 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (i >= l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_57_pre_z input )) (PreH7 : (problem_57_prefix_z input i incr decr )) ,
  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_17 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (incr <> 1)) (PreH2 : (i >= l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_18 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (incr = 1)) (PreH2 : (i >= l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_19 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr = 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition monotonic_safety_wit_20 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr <> 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "decr" ) )) # Int  |-> decr)
  **  ((( &( "incr" ) )) # Int  |-> incr)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition monotonic_entail_wit_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input 1 1 1 ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  TT && emp 
|--
  “ (problem_57_prefix_z input 1 1 1 ) ”
  &&  emp
).

Definition monotonic_entail_wit_1_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (PreH1 : (1 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_57_pre_z input )) ,
  (problem_57_prefix_z input 1 1 1 )
.

Definition monotonic_entail_wit_2_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input (i + 1 ) incr 0 ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_prefix_z input (i + 1 ) incr 0 ) ”
  &&  emp
).

Definition monotonic_entail_wit_2_1_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) > (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_prefix_z input (i + 1 ) incr 0 )
.

Definition monotonic_entail_wit_2_2 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input (i + 1 ) 0 decr ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_prefix_z input (i + 1 ) 0 decr ) ”
  &&  emp
).

Definition monotonic_entail_wit_2_2_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_prefix_z input (i + 1 ) 0 decr )
.

Definition monotonic_entail_wit_2_3 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input (i + 1 ) incr decr ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_prefix_z input (i + 1 ) incr decr ) ”
  &&  emp
).

Definition monotonic_entail_wit_2_3_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) <= (Znth (i - 1 ) input 0))) (PreH2 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH3 : (i < l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_prefix_z input (i + 1 ) incr decr )
.

Definition monotonic_return_wit_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr <> 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (problem_57_spec_z input 0 ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr <> 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_spec_z input 0 ) ”
  &&  emp
).

Definition monotonic_return_wit_1_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr <> 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_spec_z input 0 )
.

Definition monotonic_return_wit_2 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (incr = 1)) (PreH2 : (i >= l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (problem_57_spec_z input 1 ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (incr = 1)) (PreH2 : (i >= l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_spec_z input 1 ) ”
  &&  emp
).

Definition monotonic_return_wit_2_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (incr = 1)) (PreH2 : (i >= l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_spec_z input 1 )
.

Definition monotonic_return_wit_3 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr = 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (problem_57_spec_z input 1 ) ”
  &&  (IntArray.full l_pre l_size_pre input )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr = 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  TT && emp 
|--
  “ (problem_57_spec_z input 1 ) ”
  &&  emp
).

Definition monotonic_return_wit_3_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (decr = 1)) (PreH2 : (incr <> 1)) (PreH3 : (i >= l_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= l_size_pre)) (PreH6 : (l_size_pre < INT_MAX)) (PreH7 : ((Zlength (input)) = l_size_pre)) (PreH8 : (problem_57_pre_z input )) (PreH9 : (problem_57_prefix_z input i incr decr )) ,
  (problem_57_spec_z input 1 )
.

Definition monotonic_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_57_pre_z input )) (PreH7 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input )
.

Definition monotonic_partial_solve_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_57_pre_z input )) (PreH7 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) input 0))
  **  (IntArray.missing_i l_pre (i - 1 ) 0 l_size_pre input )
.

Definition monotonic_partial_solve_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ ((Znth i input 0) < (Znth (i - 1 ) input 0)) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input )
.

Definition monotonic_partial_solve_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ ((Znth i input 0) >= (Znth (i - 1 ) input 0)) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input )
.

Definition monotonic_partial_solve_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) < (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ ((Znth i input 0) < (Znth (i - 1 ) input 0)) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) input 0))
  **  (IntArray.missing_i l_pre (i - 1 ) 0 l_size_pre input )
.

Definition monotonic_partial_solve_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (incr: Z) (decr: Z) (i: Z) (PreH1 : ((Znth i input 0) >= (Znth (i - 1 ) input 0))) (PreH2 : (i < l_size_pre)) (PreH3 : (1 <= i)) (PreH4 : (i <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_57_pre_z input )) (PreH8 : (problem_57_prefix_z input i incr decr )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ ((Znth i input 0) >= (Znth (i - 1 ) input 0)) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_57_pre_z input ) ” 
  &&  “ (problem_57_prefix_z input i incr decr ) ”
  &&  (((l_pre + ((i - 1 ) * sizeof(INT)))) # Int  |-> (Znth (i - 1 ) input 0))
  **  (IntArray.missing_i l_pre (i - 1 ) 0 l_size_pre input )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_monotonic_safety_wit_1 : monotonic_safety_wit_1.
Axiom proof_of_monotonic_safety_wit_2 : monotonic_safety_wit_2.
Axiom proof_of_monotonic_safety_wit_3 : monotonic_safety_wit_3.
Axiom proof_of_monotonic_safety_wit_4 : monotonic_safety_wit_4.
Axiom proof_of_monotonic_safety_wit_5 : monotonic_safety_wit_5.
Axiom proof_of_monotonic_safety_wit_6 : monotonic_safety_wit_6.
Axiom proof_of_monotonic_safety_wit_7 : monotonic_safety_wit_7.
Axiom proof_of_monotonic_safety_wit_8 : monotonic_safety_wit_8.
Axiom proof_of_monotonic_safety_wit_9 : monotonic_safety_wit_9.
Axiom proof_of_monotonic_safety_wit_10 : monotonic_safety_wit_10.
Axiom proof_of_monotonic_safety_wit_11 : monotonic_safety_wit_11.
Axiom proof_of_monotonic_safety_wit_12 : monotonic_safety_wit_12.
Axiom proof_of_monotonic_safety_wit_13 : monotonic_safety_wit_13.
Axiom proof_of_monotonic_safety_wit_14 : monotonic_safety_wit_14.
Axiom proof_of_monotonic_safety_wit_15 : monotonic_safety_wit_15.
Axiom proof_of_monotonic_safety_wit_16 : monotonic_safety_wit_16.
Axiom proof_of_monotonic_safety_wit_17 : monotonic_safety_wit_17.
Axiom proof_of_monotonic_safety_wit_18 : monotonic_safety_wit_18.
Axiom proof_of_monotonic_safety_wit_19 : monotonic_safety_wit_19.
Axiom proof_of_monotonic_safety_wit_20 : monotonic_safety_wit_20.
Axiom proof_of_monotonic_entail_wit_1 : monotonic_entail_wit_1.
Axiom proof_of_monotonic_entail_wit_2_1 : monotonic_entail_wit_2_1.
Axiom proof_of_monotonic_entail_wit_2_2 : monotonic_entail_wit_2_2.
Axiom proof_of_monotonic_entail_wit_2_3 : monotonic_entail_wit_2_3.
Axiom proof_of_monotonic_return_wit_1 : monotonic_return_wit_1.
Axiom proof_of_monotonic_return_wit_2 : monotonic_return_wit_2.
Axiom proof_of_monotonic_return_wit_3 : monotonic_return_wit_3.
Axiom proof_of_monotonic_partial_solve_wit_1 : monotonic_partial_solve_wit_1.
Axiom proof_of_monotonic_partial_solve_wit_2 : monotonic_partial_solve_wit_2.
Axiom proof_of_monotonic_partial_solve_wit_3 : monotonic_partial_solve_wit_3.
Axiom proof_of_monotonic_partial_solve_wit_4 : monotonic_partial_solve_wit_4.
Axiom proof_of_monotonic_partial_solve_wit_5 : monotonic_partial_solve_wit_5.
Axiom proof_of_monotonic_partial_solve_wit_6 : monotonic_partial_solve_wit_6.

End VC_Correct.
