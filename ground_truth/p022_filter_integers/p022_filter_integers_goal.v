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
Require Import p022_filter_integers.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function filter_integers -----*)

Definition filter_integers_safety_wit_1 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : ((Zlength (tags)) = values_size_pre)) (PreH5 : ((Zlength (values)) = values_size_pre)) (PreH6 : (problem_22_pre_c tags values )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_2 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= values_size_pre)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : ((Zlength (tags)) = values_size_pre)) (PreH6 : ((Zlength (values)) = values_size_pre)) (PreH7 : (problem_22_pre_c tags values )) ,
  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_3 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ False ”
.

Definition filter_integers_safety_wit_4 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_5 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_6 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < values_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : ((Zlength (tags)) = values_size_pre)) (PreH6 : ((Zlength (values)) = values_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_22_pre_c tags values )) (PreH13 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.full types_pre values_size_pre tags )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition filter_integers_safety_wit_7 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
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

Definition filter_integers_safety_wit_8 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
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

Definition filter_integers_safety_wit_9 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
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

Definition filter_integers_safety_wit_10 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.full types_pre values_size_pre tags )
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition filter_integers_entail_wit_1 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  (IntArray.undef_full retval_2 values_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  EX (output: (@list Z)) ,
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= values_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (output)) = 0) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values 0 output ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg retval_2 0 0 output )
  **  (IntArray.undef_seg retval_2 0 values_size_pre )
) \/
(
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  TT && emp 
|--
  “ (problem_22_prefix_c tags values 0 (@nil Z) ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ”
  &&  emp
).

Definition filter_integers_entail_wit_1_split_goal_1 := 
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  (problem_22_prefix_c tags values 0 (@nil Z) )
.

Definition filter_integers_entail_wit_1_split_goal_2 := 
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= values_size_pre)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (problem_22_pre_c tags values )) ,
  ((Zlength ((@nil Z))) = 0)
.

Definition filter_integers_entail_wit_2_1 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  (IntArray.seg data 0 (output_size + 1 ) (app (output_2) ((cons ((Znth i values 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= values_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (output)) = (output_size + 1 )) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values (i + 1 ) output ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 (output_size + 1 ) output )
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
) \/
(
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  TT && emp 
|--
  “ (problem_22_prefix_c tags values (i + 1 ) (app (output_2) ((cons ((Znth i values 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (output_2) ((cons ((Znth i values 0)) ((@nil Z))))))) = (output_size + 1 )) ”
  &&  emp
).

Definition filter_integers_entail_wit_2_1_split_goal_1 := 
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  (problem_22_prefix_c tags values (i + 1 ) (app (output_2) ((cons ((Znth i values 0)) ((@nil Z))))) )
.

Definition filter_integers_entail_wit_2_1_split_goal_2 := 
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  ((Zlength ((app (output_2) ((cons ((Znth i values 0)) ((@nil Z))))))) = (output_size + 1 ))
.

Definition filter_integers_entail_wit_2_2 := 
(
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output_2 )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  EX (output: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values (i + 1 ) output ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
) \/
(
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  TT && emp 
|--
  “ (problem_22_prefix_c tags values (i + 1 ) output_2 ) ”
  &&  emp
).

Definition filter_integers_entail_wit_2_2_split_goal_1 := 
forall (values_size_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) <> 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output_2)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output_2 )) ,
  (problem_22_prefix_c tags values (i + 1 ) output_2 )
.

Definition filter_integers_return_wit_1 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output_2: (@list Z)) (output_size: Z) (i: Z) (data_2: Z) (out: Z) (PreH1 : (i >= values_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : ((Zlength (tags)) = values_size_pre)) (PreH6 : ((Zlength (values)) = values_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output_2)) = output_size)) (PreH12 : (problem_22_pre_c tags values )) (PreH13 : (problem_22_prefix_c tags values i output_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data_2 0 output_size output_2 )
  **  (IntArray.undef_seg data_2 output_size values_size_pre )
|--
  (EX (size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data = 0) ” 
  &&  “ (size = 0) ”
  &&  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size))
  ||
  (EX (output: (@list Z))  (size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= values_size_pre) ” 
  &&  “ ((Zlength (output)) = size) ” 
  &&  “ (problem_22_spec_c tags values output ) ”
  &&  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (IntArray.seg data 0 size output )
  **  (IntArray.undef_seg data size values_size_pre ))
.

Definition filter_integers_partial_solve_wit_1 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (PreH1 : (0 <= values_size_pre)) (PreH2 : (values_size_pre < INT_MAX)) (PreH3 : ((Zlength (tags)) = values_size_pre)) (PreH4 : ((Zlength (values)) = values_size_pre)) (PreH5 : (problem_22_pre_c tags values )) ,
  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (problem_22_pre_c tags values ) ”
  &&  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
.

Definition filter_integers_partial_solve_wit_2_pure := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : ((Zlength (tags)) = values_size_pre)) (PreH5 : ((Zlength (values)) = values_size_pre)) (PreH6 : (problem_22_pre_c tags values )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "values_size" ) )) # Int  |-> values_size_pre)
  **  ((( &( "int_values" ) )) # Ptr  |-> int_values_pre)
  **  ((( &( "types" ) )) # Ptr  |-> types_pre)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ”
.

Definition filter_integers_partial_solve_wit_2_aux := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= values_size_pre)) (PreH3 : (values_size_pre < INT_MAX)) (PreH4 : ((Zlength (tags)) = values_size_pre)) (PreH5 : ((Zlength (values)) = values_size_pre)) (PreH6 : (problem_22_pre_c tags values )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
|--
  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= values_size_pre) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (problem_22_pre_c tags values ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
.

Definition filter_integers_partial_solve_wit_2 := filter_integers_partial_solve_wit_2_pure -> filter_integers_partial_solve_wit_2_aux.

Definition filter_integers_partial_solve_wit_3 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : (i < values_size_pre)) (PreH2 : (out <> 0)) (PreH3 : (data <> 0)) (PreH4 : (values_size_pre < INT_MAX)) (PreH5 : ((Zlength (tags)) = values_size_pre)) (PreH6 : ((Zlength (values)) = values_size_pre)) (PreH7 : (0 <= i)) (PreH8 : (i <= values_size_pre)) (PreH9 : (0 <= output_size)) (PreH10 : (output_size <= i)) (PreH11 : ((Zlength (output)) = output_size)) (PreH12 : (problem_22_pre_c tags values )) (PreH13 : (problem_22_prefix_c tags values i output )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full types_pre values_size_pre tags )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ (i < values_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values i output ) ”
  &&  (((types_pre + (i * sizeof(INT)))) # Int  |-> (Znth i tags 0))
  **  (IntArray.missing_i types_pre i 0 values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
.

Definition filter_integers_partial_solve_wit_4 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((Znth i tags 0) = 0) ” 
  &&  “ (i < values_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values i output ) ”
  &&  (((int_values_pre + (i * sizeof(INT)))) # Int  |-> (Znth i values 0))
  **  (IntArray.missing_i int_values_pre i 0 values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
.

Definition filter_integers_partial_solve_wit_5 := 
forall (values_size_pre: Z) (int_values_pre: Z) (types_pre: Z) (values: (@list Z)) (tags: (@list Z)) (output: (@list Z)) (output_size: Z) (i: Z) (data: Z) (out: Z) (PreH1 : ((Znth i tags 0) = 0)) (PreH2 : (i < values_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (values_size_pre < INT_MAX)) (PreH6 : ((Zlength (tags)) = values_size_pre)) (PreH7 : ((Zlength (values)) = values_size_pre)) (PreH8 : (0 <= i)) (PreH9 : (i <= values_size_pre)) (PreH10 : (0 <= output_size)) (PreH11 : (output_size <= i)) (PreH12 : ((Zlength (output)) = output_size)) (PreH13 : (problem_22_pre_c tags values )) (PreH14 : (problem_22_prefix_c tags values i output )) ,
  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
  **  (IntArray.undef_seg data output_size values_size_pre )
|--
  “ ((Znth i tags 0) = 0) ” 
  &&  “ (i < values_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (values_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (tags)) = values_size_pre) ” 
  &&  “ ((Zlength (values)) = values_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= values_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ ((Zlength (output)) = output_size) ” 
  &&  “ (problem_22_pre_c tags values ) ” 
  &&  “ (problem_22_prefix_c tags values i output ) ”
  &&  (((data + (output_size * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg data (output_size + 1 ) values_size_pre )
  **  (IntArray.full int_values_pre values_size_pre values )
  **  (IntArray.full types_pre values_size_pre tags )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg data 0 output_size output )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_filter_integers_safety_wit_1 : filter_integers_safety_wit_1.
Axiom proof_of_filter_integers_safety_wit_2 : filter_integers_safety_wit_2.
Axiom proof_of_filter_integers_safety_wit_3 : filter_integers_safety_wit_3.
Axiom proof_of_filter_integers_safety_wit_4 : filter_integers_safety_wit_4.
Axiom proof_of_filter_integers_safety_wit_5 : filter_integers_safety_wit_5.
Axiom proof_of_filter_integers_safety_wit_6 : filter_integers_safety_wit_6.
Axiom proof_of_filter_integers_safety_wit_7 : filter_integers_safety_wit_7.
Axiom proof_of_filter_integers_safety_wit_8 : filter_integers_safety_wit_8.
Axiom proof_of_filter_integers_safety_wit_9 : filter_integers_safety_wit_9.
Axiom proof_of_filter_integers_safety_wit_10 : filter_integers_safety_wit_10.
Axiom proof_of_filter_integers_entail_wit_1 : filter_integers_entail_wit_1.
Axiom proof_of_filter_integers_entail_wit_2_1 : filter_integers_entail_wit_2_1.
Axiom proof_of_filter_integers_entail_wit_2_2 : filter_integers_entail_wit_2_2.
Axiom proof_of_filter_integers_return_wit_1 : filter_integers_return_wit_1.
Axiom proof_of_filter_integers_partial_solve_wit_1 : filter_integers_partial_solve_wit_1.
Axiom proof_of_filter_integers_partial_solve_wit_2_pure : filter_integers_partial_solve_wit_2_pure.
Axiom proof_of_filter_integers_partial_solve_wit_2 : filter_integers_partial_solve_wit_2.
Axiom proof_of_filter_integers_partial_solve_wit_3 : filter_integers_partial_solve_wit_3.
Axiom proof_of_filter_integers_partial_solve_wit_4 : filter_integers_partial_solve_wit_4.
Axiom proof_of_filter_integers_partial_solve_wit_5 : filter_integers_partial_solve_wit_5.

End VC_Correct.
