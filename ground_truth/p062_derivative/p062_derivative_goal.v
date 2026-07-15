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
Require Import p062_derivative.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function derivative -----*)

Definition derivative_safety_wit_1 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (PreH1 : (1 <= xs_size_pre)) (PreH2 : (xs_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = xs_size_pre)) (PreH4 : (problem_62_pre_z input )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.undef_full out_pre (xs_size_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition derivative_safety_wit_2 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition derivative_safety_wit_3 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition derivative_safety_wit_4 := 
(
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((i * (Znth i input 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth i input 0) )) ”
) \/
(
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((i * (Znth i input 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * (Znth i input 0) )) ”
).

Definition derivative_safety_wit_4_split_goal_1 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((i * (Znth i input 0) ) <= INT_MAX) ”
.

Definition derivative_safety_wit_4_split_goal_2 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((INT_MIN) <= (i * (Znth i input 0) )) ”
.

Definition derivative_safety_wit_5 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.seg out_pre 0 ((i - 1 ) + 1 ) (app (output) ((cons ((i * (Znth i input 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((i - 1 ) + 1 ) (xs_size_pre - 1 ) )
  **  (IntArray.full xs_pre xs_size_pre input )
  **  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition derivative_safety_wit_6 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ ((xs_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (xs_size_pre - 1 )) ”
.

Definition derivative_safety_wit_7 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  ((( &( "xs" ) )) # Ptr  |-> xs_pre)
  **  ((( &( "xs_size" ) )) # Int  |-> xs_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition derivative_entail_wit_1 := 
(
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (PreH1 : (1 <= xs_size_pre)) (PreH2 : (xs_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = xs_size_pre)) (PreH4 : (problem_62_pre_z input )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.undef_full out_pre (xs_size_pre - 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = (1 - 1 )) ” 
  &&  “ (problem_62_prefix_z input 1 output ) ”
  &&  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (1 - 1 ) output )
  **  (IntArray.undef_seg out_pre (1 - 1 ) (xs_size_pre - 1 ) )
) \/
(
forall (out_pre: Z) (xs_size_pre: Z) (input: (@list Z)) (PreH1 : (1 <= xs_size_pre)) (PreH2 : (xs_size_pre < INT_MAX)) (PreH3 : ((Zlength (input)) = xs_size_pre)) (PreH4 : (problem_62_pre_z input )) ,
  (IntArray.undef_full out_pre (xs_size_pre - 1 ) )
|--
  EX (output: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = (1 - 1 )) ” 
  &&  “ (problem_62_prefix_z input 1 output ) ”
  &&  (IntArray.seg out_pre 0 (1 - 1 ) output )
  **  (IntArray.undef_seg out_pre (1 - 1 ) (xs_size_pre - 1 ) )
).

Definition derivative_entail_wit_2 := 
(
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  (IntArray.seg out_pre 0 ((i - 1 ) + 1 ) (app (output_2) ((cons ((i * (Znth i input 0) )) ((@nil Z))))) )
  **  (IntArray.undef_seg out_pre ((i - 1 ) + 1 ) (xs_size_pre - 1 ) )
  **  (IntArray.full xs_pre xs_size_pre input )
|--
  EX (output: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = ((i + 1 ) - 1 )) ” 
  &&  “ (problem_62_prefix_z input (i + 1 ) output ) ”
  &&  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 ((i + 1 ) - 1 ) output )
  **  (IntArray.undef_seg out_pre ((i + 1 ) - 1 ) (xs_size_pre - 1 ) )
) \/
(
forall (out_pre: Z) (xs_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  (IntArray.seg out_pre 0 ((i - 1 ) + 1 ) (app (output_2) ((cons ((i * (Znth i input 0) )) ((@nil Z))))) )
|--
  EX (output: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = ((i + 1 ) - 1 )) ” 
  &&  “ (problem_62_prefix_z input (i + 1 ) output ) ”
  &&  (IntArray.seg out_pre 0 ((i + 1 ) - 1 ) output )
).

Definition derivative_return_wit_1 := 
(
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output_2 )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  EX (output: (@list Z)) ,
  “ ((xs_size_pre - 1 ) = (xs_size_pre - 1 )) ” 
  &&  “ ((Zlength (output)) = (xs_size_pre - 1 )) ” 
  &&  “ (problem_62_spec_z input output ) ”
  &&  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.full out_pre (xs_size_pre - 1 ) output )
) \/
(
forall (xs_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  TT && emp 
|--
  “ (problem_62_spec_z input output_2 ) ” 
  &&  “ ((Zlength (output_2)) = (xs_size_pre - 1 )) ”
  &&  emp
).

Definition derivative_return_wit_1_split_goal_1 := 
forall (xs_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  (problem_62_spec_z input output_2 )
.

Definition derivative_return_wit_1_split_goal_2 := 
forall (xs_size_pre: Z) (input: (@list Z)) (output_2: (@list Z)) (i: Z) (PreH1 : (i >= xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output_2)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output_2 )) ,
  ((Zlength (output_2)) = (xs_size_pre - 1 ))
.

Definition derivative_partial_solve_wit_1 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ (i < xs_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = (i - 1 )) ” 
  &&  “ (problem_62_prefix_z input i output ) ”
  &&  (((xs_pre + (i * sizeof(INT)))) # Int  |-> (Znth i input 0))
  **  (IntArray.missing_i xs_pre i 0 xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
.

Definition derivative_partial_solve_wit_2 := 
forall (out_pre: Z) (xs_size_pre: Z) (xs_pre: Z) (input: (@list Z)) (output: (@list Z)) (i: Z) (PreH1 : (i < xs_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= xs_size_pre)) (PreH4 : (xs_size_pre < INT_MAX)) (PreH5 : ((Zlength (input)) = xs_size_pre)) (PreH6 : (problem_62_pre_z input )) (PreH7 : ((Zlength (output)) = (i - 1 ))) (PreH8 : (problem_62_prefix_z input i output )) ,
  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
  **  (IntArray.undef_seg out_pre (i - 1 ) (xs_size_pre - 1 ) )
|--
  “ (i < xs_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= xs_size_pre) ” 
  &&  “ (xs_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (input)) = xs_size_pre) ” 
  &&  “ (problem_62_pre_z input ) ” 
  &&  “ ((Zlength (output)) = (i - 1 )) ” 
  &&  “ (problem_62_prefix_z input i output ) ”
  &&  (((out_pre + ((i - 1 ) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg out_pre ((i - 1 ) + 1 ) (xs_size_pre - 1 ) )
  **  (IntArray.full xs_pre xs_size_pre input )
  **  (IntArray.seg out_pre 0 (i - 1 ) output )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_derivative_safety_wit_1 : derivative_safety_wit_1.
Axiom proof_of_derivative_safety_wit_2 : derivative_safety_wit_2.
Axiom proof_of_derivative_safety_wit_3 : derivative_safety_wit_3.
Axiom proof_of_derivative_safety_wit_4 : derivative_safety_wit_4.
Axiom proof_of_derivative_safety_wit_5 : derivative_safety_wit_5.
Axiom proof_of_derivative_safety_wit_6 : derivative_safety_wit_6.
Axiom proof_of_derivative_safety_wit_7 : derivative_safety_wit_7.
Axiom proof_of_derivative_entail_wit_1 : derivative_entail_wit_1.
Axiom proof_of_derivative_entail_wit_2 : derivative_entail_wit_2.
Axiom proof_of_derivative_return_wit_1 : derivative_return_wit_1.
Axiom proof_of_derivative_partial_solve_wit_1 : derivative_partial_solve_wit_1.
Axiom proof_of_derivative_partial_solve_wit_2 : derivative_partial_solve_wit_2.

End VC_Correct.
