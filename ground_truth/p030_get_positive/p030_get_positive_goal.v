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
Require Import p030_get_positive.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function get_positive -----*)

Definition get_positive_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= l_size_pre)) (PreH3 : (l_size_pre < INT_MAX)) (PreH4 : ((Zlength (input)) = l_size_pre)) (PreH5 : (problem_30_pre_z input )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_positive_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= l_size_pre)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (problem_30_pre_z input )) ,
  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_positive_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ False ”
.

Definition get_positive_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_positive_safety_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_positive_safety_wit_6 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= l_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : ((Zlength (output)) = output_size)) (PreH11 : (problem_30_pre_z input )) (PreH12 : (problem_30_prefix_z input i output )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition get_positive_safety_wit_7 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i input 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition get_positive_safety_wit_8 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i input 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition get_positive_safety_wit_9 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i input 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> (output_size + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_positive_safety_wit_10 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition get_positive_entail_wit_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
|--
  EX (output: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (output)) = 0) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input 0 output ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
  **  (IntArray.seg retval_2 0 0 output )
  **  (IntArray.undef_seg retval_2 0 l_size_pre )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  TT && emp 
|--
  “ (problem_30_prefix_z input 0 (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition get_positive_entail_wit_1_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  (problem_30_prefix_z input 0 (@nil Z) )
.

Definition get_positive_entail_wit_1_split_goal_2 := 
forall (l_size_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= l_size_pre)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (problem_30_pre_z input )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition get_positive_entail_wit_2_1 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_2) ((cons ((Znth i input 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (output)) = (output_size + 1 )) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input (i + 1 ) output ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
  **  (IntArray.seg data 0 (output_size + 1 ) output )
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  TT && emp 
|--
  “ (problem_30_prefix_z input (i + 1 ) (app (output_2) ((cons ((Znth i input 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (output_2) ((cons ((Znth i input 0)) ((@nil Z))))))) = (output_size + 1 )) ”
  &&  emp
).

Definition get_positive_entail_wit_2_1_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  (problem_30_prefix_z input (i + 1 ) (app (output_2) ((cons ((Znth i input 0)) ((@nil Z))))) )
.

Definition get_positive_entail_wit_2_1_split_goal_2 := 
forall (l_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  ((Zlength ((app (output_2) ((cons ((Znth i input 0)) ((@nil Z))))))) = (output_size + 1 ))
.

Definition get_positive_entail_wit_2_2 := 
(
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output_2 )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input (i + 1 ) output ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
) \/
(
forall (l_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  TT && emp 
|--
  “ (problem_30_prefix_z input (i + 1 ) output_2 ) ”
  &&  emp
).

Definition get_positive_entail_wit_2_2_split_goal_1 := 
forall (l_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) <= 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output_2 )) ,
  (problem_30_prefix_z input (i + 1 ) output_2 )
.

Definition get_positive_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data_2: Z) (out: Z) (PreH1 : (i >= l_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= l_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : ((Zlength (output_2)) = output_size)) (PreH11 : (problem_30_pre_z input )) (PreH12 : (problem_30_prefix_z input i output_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full l_pre l_size_pre input )
  **  (IntArray.seg data_2 0 output_size output_2 )
  **  (IntArray.undef_seg data_2 output_size l_size_pre )
|--
  (EX (size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data = 0) ” 
  &&  “ (size = 0) ”
  &&  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size))
  ||
  (EX (output: (@list Z))  (size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= l_size_pre) ” 
  &&  “ ((Zlength (output)) = size) ” 
  &&  “ (problem_30_spec_z input output ) ”
  &&  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size output )
  **  (IntArray.undef_seg data size l_size_pre ))
.

Definition get_positive_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (PreH1 : (0 <= l_size_pre)) (PreH2 : (l_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = l_size_pre)) (PreH4 : (problem_30_pre_z input )) ,
  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_30_pre_z input ) ”
  &&  (IntArray.full l_pre l_size_pre input )
.

Definition get_positive_partial_solve_wit_2_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= l_size_pre)) (PreH3 : (l_size_pre < INT_MAX)) (PreH4 : ((Zlength (input)) = l_size_pre)) (PreH5 : (problem_30_pre_z input )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
.

Definition get_positive_partial_solve_wit_2_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= l_size_pre)) (PreH3 : (l_size_pre < INT_MAX)) (PreH4 : ((Zlength (input)) = l_size_pre)) (PreH5 : (problem_30_pre_z input )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
|--
  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (problem_30_pre_z input ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
.

Definition get_positive_partial_solve_wit_2 := get_positive_partial_solve_wit_2_pure -> get_positive_partial_solve_wit_2_aux.

Definition get_positive_partial_solve_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < l_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (l_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = l_size_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= l_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : ((Zlength (output)) = output_size)) (PreH11 : (problem_30_pre_z input )) (PreH12 : (problem_30_prefix_z input i output )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full l_pre l_size_pre input )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  “ (i < l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input i output ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
.

Definition get_positive_partial_solve_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  “ ((Znth i input 0) > 0) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input i output ) ”
  &&  (((l_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
.

Definition get_positive_partial_solve_wit_5 := 
forall (l_size_pre: Z) (l_pre: Z) (input: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i input 0) > 0)) (PreH2 : (i < l_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (l_size_pre < INT_MAX)) (PreH6 : ((Zlength (input)) = l_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= l_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_30_pre_z input )) (PreH13 : (problem_30_prefix_z input i output )) ,
  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size l_size_pre )
|--
  “ ((Znth i input 0) > 0) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_30_pre_z input ) ” 
  &&  “ (problem_30_prefix_z input i output ) ”
  &&  (((data + (output_size * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_get_positive_safety_wit_1 : get_positive_safety_wit_1.
Axiom proof_of_get_positive_safety_wit_2 : get_positive_safety_wit_2.
Axiom proof_of_get_positive_safety_wit_3 : get_positive_safety_wit_3.
Axiom proof_of_get_positive_safety_wit_4 : get_positive_safety_wit_4.
Axiom proof_of_get_positive_safety_wit_5 : get_positive_safety_wit_5.
Axiom proof_of_get_positive_safety_wit_6 : get_positive_safety_wit_6.
Axiom proof_of_get_positive_safety_wit_7 : get_positive_safety_wit_7.
Axiom proof_of_get_positive_safety_wit_8 : get_positive_safety_wit_8.
Axiom proof_of_get_positive_safety_wit_9 : get_positive_safety_wit_9.
Axiom proof_of_get_positive_safety_wit_10 : get_positive_safety_wit_10.
Axiom proof_of_get_positive_entail_wit_1 : get_positive_entail_wit_1.
Axiom proof_of_get_positive_entail_wit_2_1 : get_positive_entail_wit_2_1.
Axiom proof_of_get_positive_entail_wit_2_2 : get_positive_entail_wit_2_2.
Axiom proof_of_get_positive_return_wit_1 : get_positive_return_wit_1.
Axiom proof_of_get_positive_partial_solve_wit_1 : get_positive_partial_solve_wit_1.
Axiom proof_of_get_positive_partial_solve_wit_2_pure : get_positive_partial_solve_wit_2_pure.
Axiom proof_of_get_positive_partial_solve_wit_2 : get_positive_partial_solve_wit_2.
Axiom proof_of_get_positive_partial_solve_wit_3 : get_positive_partial_solve_wit_3.
Axiom proof_of_get_positive_partial_solve_wit_4 : get_positive_partial_solve_wit_4.
Axiom proof_of_get_positive_partial_solve_wit_5 : get_positive_partial_solve_wit_5.

End VC_Correct.
