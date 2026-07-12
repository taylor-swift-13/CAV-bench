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
Require Import SimpleC.StdLib.string_lib.
Require Import p160_do_algebra.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function operator_code -----*)

Definition operator_code_safety_wit_1 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition operator_code_safety_wit_2 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (42 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 42) ”
.

Definition operator_code_safety_wit_3 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH2 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition operator_code_safety_wit_4 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH2 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (42 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 42) ”
.

Definition operator_code_safety_wit_5 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 1 (c_string (payload)) 0) = 42)) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition operator_code_safety_wit_6 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 1 (c_string (payload)) 0) <> 42)) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition operator_code_safety_wit_7 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH2 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition operator_code_safety_wit_8 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH2 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (47 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 47) ”
.

Definition operator_code_safety_wit_9 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 47)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition operator_code_safety_wit_10 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition operator_code_safety_wit_11 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (43 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 43) ”
.

Definition operator_code_safety_wit_12 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 43)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition operator_code_safety_wit_13 := 
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 43)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  ((( &( "op" ) )) # Ptr  |-> op_pre)
  **  (store_string op_pre payload )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition operator_code_return_wit_1 := 
(
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) <> 43)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  (store_string op_pre payload )
|--
  “ (1 = (operator_code_payload_160 (payload))) ”
  &&  (store_string op_pre payload )
) \/
(
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 43)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH4 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH5 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (1 = (operator_code_payload_160 (payload))) ”
  &&  emp
).

Definition operator_code_return_wit_1_split_goal_1 := 
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 43)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH4 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH5 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (1 = (operator_code_payload_160 (payload))) ”
.

Definition operator_code_return_wit_2 := 
(
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 43)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  (store_string op_pre payload )
|--
  “ (0 = (operator_code_payload_160 (payload))) ”
  &&  (store_string op_pre payload )
) \/
(
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 43)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH4 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH5 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (0 = (operator_code_payload_160 (payload))) ”
  &&  emp
).

Definition operator_code_return_wit_2_split_goal_1 := 
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 43)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 47)) (PreH4 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH5 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (0 = (operator_code_payload_160 (payload))) ”
.

Definition operator_code_return_wit_3 := 
(
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 0 (c_string (payload)) 0) = 47)) (PreH2 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  (store_string op_pre payload )
|--
  “ (3 = (operator_code_payload_160 (payload))) ”
  &&  (store_string op_pre payload )
) \/
(
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (3 = (operator_code_payload_160 (payload))) ”
  &&  emp
).

Definition operator_code_return_wit_3_split_goal_1 := 
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 47)) (PreH3 : ((Znth 0 (c_string (payload)) 0) <> 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (3 = (operator_code_payload_160 (payload))) ”
.

Definition operator_code_return_wit_4 := 
(
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 1 (c_string (payload)) 0) <> 42)) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  (store_string op_pre payload )
|--
  “ (2 = (operator_code_payload_160 (payload))) ”
  &&  (store_string op_pre payload )
) \/
(
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 1 (c_string (payload)) 0) <> 42)) (PreH3 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (2 = (operator_code_payload_160 (payload))) ”
  &&  emp
).

Definition operator_code_return_wit_4_split_goal_1 := 
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 1 (c_string (payload)) 0) <> 42)) (PreH3 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (2 = (operator_code_payload_160 (payload))) ”
.

Definition operator_code_return_wit_5 := 
(
forall (op_pre: Z) (payload: (@list Z)) (PreH1 : ((Znth 1 (c_string (payload)) 0) = 42)) (PreH2 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH3 : (operator_payload_valid_160 payload )) ,
  (store_string op_pre payload )
|--
  “ (4 = (operator_code_payload_160 (payload))) ”
  &&  (store_string op_pre payload )
) \/
(
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 1 (c_string (payload)) 0) = 42)) (PreH3 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (4 = (operator_code_payload_160 (payload))) ”
  &&  emp
).

Definition operator_code_return_wit_5_split_goal_1 := 
forall (payload: (@list Z)) (PreH1 : (0 <= ((string_length (payload)) + 1 ))) (PreH2 : ((Znth 1 (c_string (payload)) 0) = 42)) (PreH3 : ((Znth 0 (c_string (payload)) 0) = 42)) (PreH4 : (operator_payload_valid_160 payload )) ,
  TT && emp 
|--
  “ (4 = (operator_code_payload_160 (payload))) ”
.

(*----- Function int_pow -----*)

Definition int_pow_safety_wit_1 := 
forall (exp_pre: Z) (base_pre: Z) (PreH1 : (0 <= exp_pre)) (PreH2 : (exp_pre < INT_MAX)) (PreH3 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition int_pow_safety_wit_2 := 
forall (exp_pre: Z) (base_pre: Z) (PreH1 : (0 <= exp_pre)) (PreH2 : (exp_pre < INT_MAX)) (PreH3 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "result" ) )) # Int  |-> 1)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition int_pow_safety_wit_3 := 
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * base_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result * base_pre )) ”
) \/
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * base_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result * base_pre )) ”
).

Definition int_pow_safety_wit_3_split_goal_1 := 
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * base_pre ) <= INT_MAX) ”
.

Definition int_pow_safety_wit_3_split_goal_2 := 
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((INT_MIN) <= (result * base_pre )) ”
.

Definition int_pow_safety_wit_4 := 
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "exp" ) )) # Int  |-> exp_pre)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "result" ) )) # Int  |-> (result * base_pre ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition int_pow_entail_wit_1 := 
(
forall (exp_pre: Z) (base_pre: Z) (PreH1 : (0 <= exp_pre)) (PreH2 : (exp_pre < INT_MAX)) (PreH3 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= exp_pre) ” 
  &&  “ (1 = (Zpow_160 (base_pre) (0))) ” 
  &&  “ (pow_prefix_safe_160 base_pre exp_pre ) ”
  &&  emp
) \/
(
forall (exp_pre: Z) (base_pre: Z) (PreH1 : (0 <= exp_pre)) (PreH2 : (exp_pre < INT_MAX)) (PreH3 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (1 = (Zpow_160 (base_pre) (0))) ”
  &&  emp
).

Definition int_pow_entail_wit_1_split_goal_1 := 
forall (exp_pre: Z) (base_pre: Z) (PreH1 : (0 <= exp_pre)) (PreH2 : (exp_pre < INT_MAX)) (PreH3 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (1 = (Zpow_160 (base_pre) (0))) ”
.

Definition int_pow_entail_wit_2 := 
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= exp_pre) ” 
  &&  “ ((result * base_pre ) = (Zpow_160 (base_pre) ((i + 1 )))) ” 
  &&  “ (pow_prefix_safe_160 base_pre exp_pre ) ”
  &&  emp
) \/
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ ((result * base_pre ) = (Zpow_160 (base_pre) ((i + 1 )))) ”
  &&  emp
).

Definition int_pow_entail_wit_2_split_goal_1 := 
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i < exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ ((result * base_pre ) = (Zpow_160 (base_pre) ((i + 1 )))) ”
.

Definition int_pow_return_wit_1 := 
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i >= exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (result = (Zpow_160 (base_pre) (exp_pre))) ”
  &&  emp
) \/
(
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i >= exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (result = (Zpow_160 (base_pre) (exp_pre))) ”
  &&  emp
).

Definition int_pow_return_wit_1_split_goal_1 := 
forall (exp_pre: Z) (base_pre: Z) (result: Z) (i: Z) (PreH1 : (i >= exp_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= exp_pre)) (PreH4 : (result = (Zpow_160 (base_pre) (i)))) (PreH5 : (pow_prefix_safe_160 base_pre exp_pre )) ,
  TT && emp 
|--
  “ (result = (Zpow_160 (base_pre) (exp_pre))) ”
.

(*----- Function eval_range -----*)

Definition eval_range_safety_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_range_safety_wit_4 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : (ops_size_pre = (Zlength (ops_l)))) (PreH7 : (nums_size_pre = (Zlength (nums_l)))) (PreH8 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH9 : (0 <= lo_pre)) (PreH10 : (lo_pre < hi_pre)) (PreH11 : (hi_pre < nums_size_pre)) (PreH12 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_range_safety_wit_5 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_6 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_7 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_8 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_9 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_10 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_11 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_12 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_13 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : (ops_size_pre = (Zlength (ops_l)))) (PreH7 : (nums_size_pre = (Zlength (nums_l)))) (PreH8 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH9 : (0 <= lo_pre)) (PreH10 : (lo_pre < hi_pre)) (PreH11 : (hi_pre < nums_size_pre)) (PreH12 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_14 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_15 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_16 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : (ops_size_pre = (Zlength (ops_l)))) (PreH7 : (nums_size_pre = (Zlength (nums_l)))) (PreH8 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH9 : (0 <= lo_pre)) (PreH10 : (lo_pre < hi_pre)) (PreH11 : (hi_pre < nums_size_pre)) (PreH12 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_17 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_18 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_19 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition eval_range_safety_wit_20 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_21 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_range_safety_wit_22 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + retval_2 )) ”
).

Definition eval_range_safety_wit_22_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval + retval_2 ) <= INT_MAX) ”
.

Definition eval_range_safety_wit_22_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((INT_MIN) <= (retval + retval_2 )) ”
.

Definition eval_range_safety_wit_23 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - retval_2 )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - retval_2 )) ”
).

Definition eval_range_safety_wit_23_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval - retval_2 ) <= INT_MAX) ”
.

Definition eval_range_safety_wit_23_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((INT_MIN) <= (retval - retval_2 )) ”
.

Definition eval_range_safety_wit_24 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : (ops_size_pre = (Zlength (ops_l)))) (PreH4 : (nums_size_pre = (Zlength (nums_l)))) (PreH5 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH6 : (0 <= lo_pre)) (PreH7 : (lo_pre < hi_pre)) (PreH8 : (hi_pre < nums_size_pre)) (PreH9 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_25 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : (ops_size_pre = (Zlength (ops_l)))) (PreH4 : (nums_size_pre = (Zlength (nums_l)))) (PreH5 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH6 : (0 <= lo_pre)) (PreH7 : (lo_pre < hi_pre)) (PreH8 : (hi_pre < nums_size_pre)) (PreH9 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_26 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition eval_range_safety_wit_27 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition eval_range_safety_wit_28 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition eval_range_safety_wit_29 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition eval_range_safety_wit_30 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_31 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_32 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_33 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_34 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_35 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_36 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_37 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_38 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_39 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_40 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_41 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_42 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition eval_range_safety_wit_43 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_44 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition eval_range_safety_wit_45 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * retval_2 )) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval * retval_2 )) ”
).

Definition eval_range_safety_wit_45_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval * retval_2 ) <= INT_MAX) ”
.

Definition eval_range_safety_wit_45_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((INT_MIN) <= (retval * retval_2 )) ”
.

Definition eval_range_safety_wit_46 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ” 
  &&  “ (retval_2 <> 0) ”
).

Definition eval_range_safety_wit_46_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (retval_2 <> (-1))) ”
.

Definition eval_range_safety_wit_46_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (retval_2 <> 0) ”
.

Definition eval_range_safety_wit_47 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH4 : (ops_size_pre = (Zlength (ops_l)))) (PreH5 : (nums_size_pre = (Zlength (nums_l)))) (PreH6 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH7 : (0 <= lo_pre)) (PreH8 : (lo_pre < hi_pre)) (PreH9 : (hi_pre < nums_size_pre)) (PreH10 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_48 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH4 : (ops_size_pre = (Zlength (ops_l)))) (PreH5 : (nums_size_pre = (Zlength (nums_l)))) (PreH6 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH7 : (0 <= lo_pre)) (PreH8 : (lo_pre < hi_pre)) (PreH9 : (hi_pre < nums_size_pre)) (PreH10 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_49 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_50 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_51 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_52 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_53 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_54 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_55 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition eval_range_safety_wit_56 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 4)) (PreH2 : (idx = (-1))) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_57 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_58 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 4)) (PreH2 : (idx = (-1))) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition eval_range_safety_wit_59 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_60 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition eval_range_safety_wit_61 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_62 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i >= hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_63 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_64 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ False ”
.

Definition eval_range_safety_wit_65 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ ((idx + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (idx + 1 )) ”
.

Definition eval_range_safety_wit_66 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition eval_range_safety_wit_67 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition eval_range_entail_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre <> hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_addsub_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ (lo_pre <= (-1)) ” 
  &&  “ ((-1) < lo_pre) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_addsub_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_4 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_5 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_2_6 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 1)) (PreH2 : ((Znth i ops_l 0) <> 0)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_3 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ”
  &&  emp
).

Definition eval_range_entail_wit_3_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ”
.

Definition eval_range_entail_wit_4 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : (ops_size_pre = (Zlength (ops_l)))) (PreH4 : (nums_size_pre = (Zlength (nums_l)))) (PreH5 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH6 : (0 <= lo_pre)) (PreH7 : (lo_pre < hi_pre)) (PreH8 : (hi_pre < nums_size_pre)) (PreH9 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_muldiv_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_muldiv_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ (lo_pre <= (-1)) ” 
  &&  “ ((-1) < lo_pre) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_4 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_5 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_5_6 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 3)) (PreH2 : ((Znth i ops_l 0) <> 2)) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_6 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ”
  &&  emp
).

Definition eval_range_entail_wit_6_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ”
.

Definition eval_range_entail_wit_7 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (PreH1 : (idx = (-1))) (PreH2 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH3 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH4 : (ops_size_pre = (Zlength (ops_l)))) (PreH5 : (nums_size_pre = (Zlength (nums_l)))) (PreH6 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH7 : (0 <= lo_pre)) (PreH8 : (lo_pre < hi_pre)) (PreH9 : (hi_pre < nums_size_pre)) (PreH10 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_pow_left_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ (lo_pre <= (-1)) ” 
  &&  “ ((-1) < lo_pre) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((-1) = (find_pow_left_prefix_160 (ops_l) (lo_pre) (lo_pre))) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_8_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) = 4)) (PreH2 : (idx = (-1))) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (i = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (i = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_8_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_entail_wit_8_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 4)) (PreH2 : (idx = (-1))) (PreH3 : (i < hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (idx = (-1))) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
  ||
  (“ (lo_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) ((i + 1 )))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l ))
.

Definition eval_range_return_wit_1 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (0 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (0 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_1_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (0 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_2 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Zpow_160 (retval_2) (retval_3)))) (PreH2 : (retval_3 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval_2 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH13 : (ops_size_pre = (Zlength (ops_l)))) (PreH14 : (nums_size_pre = (Zlength (nums_l)))) (PreH15 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH16 : (0 <= lo_pre)) (PreH17 : (lo_pre < hi_pre)) (PreH18 : (hi_pre < nums_size_pre)) (PreH19 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Zpow_160 (retval_2) (retval_3)))) (PreH2 : (retval_3 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval_2 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH13 : (ops_size_pre = (Zlength (ops_l)))) (PreH14 : (nums_size_pre = (Zlength (nums_l)))) (PreH15 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH16 : (0 <= lo_pre)) (PreH17 : (lo_pre < hi_pre)) (PreH18 : (hi_pre < nums_size_pre)) (PreH19 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_2_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval_2: Z) (retval_3: Z) (retval: Z) (PreH1 : (retval = (Zpow_160 (retval_2) (retval_3)))) (PreH2 : (retval_3 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval_2 = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH13 : (ops_size_pre = (Zlength (ops_l)))) (PreH14 : (nums_size_pre = (Zlength (nums_l)))) (PreH15 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH16 : (0 <= lo_pre)) (PreH17 : (lo_pre < hi_pre)) (PreH18 : (hi_pre < nums_size_pre)) (PreH19 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_3 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((retval ÷ retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval ÷ retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_3_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval ÷ retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_4 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((retval * retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval * retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_4_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 2)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval * retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_5 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((retval - retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval - retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_5_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) <> 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval - retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_6 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((retval + retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval + retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_6_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : ((Znth idx ops_l 0) = 0)) (PreH2 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH3 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH4 : (idx <> (-1))) (PreH5 : (i >= hi_pre)) (PreH6 : (lo_pre <= i)) (PreH7 : (i <= hi_pre)) (PreH8 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH9 : (lo_pre <= idx)) (PreH10 : (idx < i)) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((retval + retval_2 ) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_return_wit_7 := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full nums_pre nums_size_pre nums_l )
  **  (IntArray.full ops_pre ops_size_pre ops_l )
|--
  “ ((Znth lo_pre nums_l 0) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((Znth lo_pre nums_l 0) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
  &&  emp
).

Definition eval_range_return_wit_7_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (ops_size_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  TT && emp 
|--
  “ ((Znth lo_pre nums_l 0) = (eval_range_160 (ops_l) (nums_l) (lo_pre) (hi_pre))) ”
.

Definition eval_range_partial_solve_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (PreH1 : (lo_pre = hi_pre)) (PreH2 : (ops_size_pre = (Zlength (ops_l)))) (PreH3 : (nums_size_pre = (Zlength (nums_l)))) (PreH4 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH5 : (0 <= lo_pre)) (PreH6 : (lo_pre <= hi_pre)) (PreH7 : (hi_pre < nums_size_pre)) (PreH8 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (lo_pre = hi_pre) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((nums_pre + (lo_pre * sizeof(INT) ) )) # Int  |-> (Znth lo_pre nums_l 0))
  **  (IntArray.missing_i nums_pre lo_pre 0 nums_size_pre nums_l )
  **  (IntArray.full ops_pre ops_size_pre ops_l )
.

Definition eval_range_partial_solve_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : (ops_size_pre = (Zlength (ops_l)))) (PreH7 : (nums_size_pre = (Zlength (nums_l)))) (PreH8 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH9 : (0 <= lo_pre)) (PreH10 : (lo_pre < hi_pre)) (PreH11 : (hi_pre < nums_size_pre)) (PreH12 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_4 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((Znth i ops_l 0) <> 0) ” 
  &&  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_5 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 0)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((Znth i ops_l 0) <> 0) ” 
  &&  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_6_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : (ops_size_pre = (Zlength (ops_l)))) (PreH19 : (nums_size_pre = (Zlength (nums_l)))) (PreH20 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH21 : (0 <= lo_pre)) (PreH22 : (lo_pre < hi_pre)) (PreH23 : (hi_pre < nums_size_pre)) (PreH24 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
).

Definition eval_range_partial_solve_wit_6_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : (ops_size_pre = (Zlength (ops_l)))) (PreH19 : (nums_size_pre = (Zlength (nums_l)))) (PreH20 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH21 : (0 <= lo_pre)) (PreH22 : (lo_pre < hi_pre)) (PreH23 : (hi_pre < nums_size_pre)) (PreH24 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
.

Definition eval_range_partial_solve_wit_6_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_6 := eval_range_partial_solve_wit_6_pure -> eval_range_partial_solve_wit_6_aux.

Definition eval_range_partial_solve_wit_7_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : (ops_size_pre = (Zlength (ops_l)))) (PreH22 : (nums_size_pre = (Zlength (nums_l)))) (PreH23 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH24 : (0 <= lo_pre)) (PreH25 : (lo_pre < hi_pre)) (PreH26 : (hi_pre < nums_size_pre)) (PreH27 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
).

Definition eval_range_partial_solve_wit_7_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : (ops_size_pre = (Zlength (ops_l)))) (PreH22 : (nums_size_pre = (Zlength (nums_l)))) (PreH23 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH24 : (0 <= lo_pre)) (PreH25 : (lo_pre < hi_pre)) (PreH26 : (hi_pre < nums_size_pre)) (PreH27 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
.

Definition eval_range_partial_solve_wit_7_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_7 := eval_range_partial_solve_wit_7_pure -> eval_range_partial_solve_wit_7_aux.

Definition eval_range_partial_solve_wit_8 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre))) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_addsub_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (idx * sizeof(INT) ) )) # Int  |-> (Znth idx ops_l 0))
  **  (IntArray.missing_i ops_pre idx 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_9 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (idx = (-1))) (PreH6 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH7 : (ops_size_pre = (Zlength (ops_l)))) (PreH8 : (nums_size_pre = (Zlength (nums_l)))) (PreH9 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH10 : (0 <= lo_pre)) (PreH11 : (lo_pre < hi_pre)) (PreH12 : (hi_pre < nums_size_pre)) (PreH13 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_10 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (i < hi_pre)) (PreH2 : (lo_pre <= i)) (PreH3 : (i <= hi_pre)) (PreH4 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH5 : (lo_pre <= idx)) (PreH6 : (idx < i)) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_11 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((Znth i ops_l 0) <> 2) ” 
  &&  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_12 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : ((Znth i ops_l 0) <> 2)) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : (ops_size_pre = (Zlength (ops_l)))) (PreH9 : (nums_size_pre = (Zlength (nums_l)))) (PreH10 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH11 : (0 <= lo_pre)) (PreH12 : (lo_pre < hi_pre)) (PreH13 : (hi_pre < nums_size_pre)) (PreH14 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ ((Znth i ops_l 0) <> 2) ” 
  &&  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_13_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH19 : (ops_size_pre = (Zlength (ops_l)))) (PreH20 : (nums_size_pre = (Zlength (nums_l)))) (PreH21 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH22 : (0 <= lo_pre)) (PreH23 : (lo_pre < hi_pre)) (PreH24 : (hi_pre < nums_size_pre)) (PreH25 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
).

Definition eval_range_partial_solve_wit_13_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH19 : (ops_size_pre = (Zlength (ops_l)))) (PreH20 : (nums_size_pre = (Zlength (nums_l)))) (PreH21 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH22 : (0 <= lo_pre)) (PreH23 : (lo_pre < hi_pre)) (PreH24 : (hi_pre < nums_size_pre)) (PreH25 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
.

Definition eval_range_partial_solve_wit_13_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_13 := eval_range_partial_solve_wit_13_pure -> eval_range_partial_solve_wit_13_aux.

Definition eval_range_partial_solve_wit_14_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH22 : (ops_size_pre = (Zlength (ops_l)))) (PreH23 : (nums_size_pre = (Zlength (nums_l)))) (PreH24 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH25 : (0 <= lo_pre)) (PreH26 : (lo_pre < hi_pre)) (PreH27 : (hi_pre < nums_size_pre)) (PreH28 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
).

Definition eval_range_partial_solve_wit_14_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH22 : (ops_size_pre = (Zlength (ops_l)))) (PreH23 : (nums_size_pre = (Zlength (nums_l)))) (PreH24 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH25 : (0 <= lo_pre)) (PreH26 : (lo_pre < hi_pre)) (PreH27 : (hi_pre < nums_size_pre)) (PreH28 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
.

Definition eval_range_partial_solve_wit_14_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_14 := eval_range_partial_solve_wit_14_pure -> eval_range_partial_solve_wit_14_aux.

Definition eval_range_partial_solve_wit_15 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre))) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_muldiv_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (idx * sizeof(INT) ) )) # Int  |-> (Znth idx ops_l 0))
  **  (IntArray.missing_i ops_pre idx 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_16 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx = (-1))) (PreH2 : (i < hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (idx = (-1))) (PreH7 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH8 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : (ops_size_pre = (Zlength (ops_l)))) (PreH10 : (nums_size_pre = (Zlength (nums_l)))) (PreH11 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH12 : (0 <= lo_pre)) (PreH13 : (lo_pre < hi_pre)) (PreH14 : (hi_pre < nums_size_pre)) (PreH15 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (idx = (-1)) ” 
  &&  “ (i < hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (idx = (-1)) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (((ops_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i ops_l 0))
  **  (IntArray.missing_i ops_pre i 0 ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_17_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH19 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH20 : (ops_size_pre = (Zlength (ops_l)))) (PreH21 : (nums_size_pre = (Zlength (nums_l)))) (PreH22 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH23 : (0 <= lo_pre)) (PreH24 : (lo_pre < hi_pre)) (PreH25 : (hi_pre < nums_size_pre)) (PreH26 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
).

Definition eval_range_partial_solve_wit_17_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (nums_size_pre >= INT_MIN)) (PreH7 : (ops_size_pre >= INT_MIN)) (PreH8 : (idx >= INT_MIN)) (PreH9 : (hi_pre >= INT_MIN)) (PreH10 : (lo_pre >= INT_MIN)) (PreH11 : (idx <> (-1))) (PreH12 : (i >= hi_pre)) (PreH13 : (lo_pre <= i)) (PreH14 : (i <= hi_pre)) (PreH15 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH16 : (lo_pre <= idx)) (PreH17 : (idx < i)) (PreH18 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH19 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH20 : (ops_size_pre = (Zlength (ops_l)))) (PreH21 : (nums_size_pre = (Zlength (nums_l)))) (PreH22 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH23 : (0 <= lo_pre)) (PreH24 : (lo_pre < hi_pre)) (PreH25 : (hi_pre < nums_size_pre)) (PreH26 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ”
.

Definition eval_range_partial_solve_wit_17_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (PreH1 : (idx <> (-1))) (PreH2 : (i >= hi_pre)) (PreH3 : (lo_pre <= i)) (PreH4 : (i <= hi_pre)) (PreH5 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH6 : (lo_pre <= idx)) (PreH7 : (idx < i)) (PreH8 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH9 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : (ops_size_pre = (Zlength (ops_l)))) (PreH11 : (nums_size_pre = (Zlength (nums_l)))) (PreH12 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH13 : (0 <= lo_pre)) (PreH14 : (lo_pre < hi_pre)) (PreH15 : (hi_pre < nums_size_pre)) (PreH16 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre idx ) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_17 := eval_range_partial_solve_wit_17_pure -> eval_range_partial_solve_wit_17_aux.

Definition eval_range_partial_solve_wit_18_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH22 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH23 : (ops_size_pre = (Zlength (ops_l)))) (PreH24 : (nums_size_pre = (Zlength (nums_l)))) (PreH25 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH26 : (0 <= lo_pre)) (PreH27 : (lo_pre < hi_pre)) (PreH28 : (hi_pre < nums_size_pre)) (PreH29 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
).

Definition eval_range_partial_solve_wit_18_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (nums_size_pre >= INT_MIN)) (PreH8 : (ops_size_pre >= INT_MIN)) (PreH9 : (idx >= INT_MIN)) (PreH10 : (hi_pre >= INT_MIN)) (PreH11 : (lo_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH14 : (idx <> (-1))) (PreH15 : (i >= hi_pre)) (PreH16 : (lo_pre <= i)) (PreH17 : (i <= hi_pre)) (PreH18 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH19 : (lo_pre <= idx)) (PreH20 : (idx < i)) (PreH21 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH22 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH23 : (ops_size_pre = (Zlength (ops_l)))) (PreH24 : (nums_size_pre = (Zlength (nums_l)))) (PreH25 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH26 : (0 <= lo_pre)) (PreH27 : (lo_pre < hi_pre)) (PreH28 : (hi_pre < nums_size_pre)) (PreH29 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  ((( &( "right" ) )) # Int  |->_)
  **  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ”
.

Definition eval_range_partial_solve_wit_18_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH2 : (idx <> (-1))) (PreH3 : (i >= hi_pre)) (PreH4 : (lo_pre <= i)) (PreH5 : (i <= hi_pre)) (PreH6 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH7 : (lo_pre <= idx)) (PreH8 : (idx < i)) (PreH9 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH10 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : (ops_size_pre = (Zlength (ops_l)))) (PreH12 : (nums_size_pre = (Zlength (nums_l)))) (PreH13 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH14 : (0 <= lo_pre)) (PreH15 : (lo_pre < hi_pre)) (PreH16 : (hi_pre < nums_size_pre)) (PreH17 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= (idx + 1 )) ” 
  &&  “ ((idx + 1 ) <= hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l (idx + 1 ) hi_pre ) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_18 := eval_range_partial_solve_wit_18_pure -> eval_range_partial_solve_wit_18_aux.

Definition eval_range_partial_solve_wit_19_pure := 
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (pow_prefix_safe_160 retval retval_2 ) ” 
  &&  “ (retval_2 < INT_MAX) ” 
  &&  “ (0 <= retval_2) ”
) \/
(
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval_2 <= INT_MAX)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (ops_size_pre >= INT_MIN)) (PreH10 : (idx >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : (retval_2 >= INT_MIN)) (PreH15 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH16 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH17 : (idx <> (-1))) (PreH18 : (i >= hi_pre)) (PreH19 : (lo_pre <= i)) (PreH20 : (i <= hi_pre)) (PreH21 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH22 : (lo_pre <= idx)) (PreH23 : (idx < i)) (PreH24 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH25 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH26 : (ops_size_pre = (Zlength (ops_l)))) (PreH27 : (nums_size_pre = (Zlength (nums_l)))) (PreH28 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH29 : (0 <= lo_pre)) (PreH30 : (lo_pre < hi_pre)) (PreH31 : (hi_pre < nums_size_pre)) (PreH32 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 < INT_MAX) ” 
  &&  “ (pow_prefix_safe_160 retval retval_2 ) ”
).

Definition eval_range_partial_solve_wit_19_pure_split_goal_1 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval_2 <= INT_MAX)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (ops_size_pre >= INT_MIN)) (PreH10 : (idx >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : (retval_2 >= INT_MIN)) (PreH15 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH16 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH17 : (idx <> (-1))) (PreH18 : (i >= hi_pre)) (PreH19 : (lo_pre <= i)) (PreH20 : (i <= hi_pre)) (PreH21 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH22 : (lo_pre <= idx)) (PreH23 : (idx < i)) (PreH24 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH25 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH26 : (ops_size_pre = (Zlength (ops_l)))) (PreH27 : (nums_size_pre = (Zlength (nums_l)))) (PreH28 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH29 : (0 <= lo_pre)) (PreH30 : (lo_pre < hi_pre)) (PreH31 : (hi_pre < nums_size_pre)) (PreH32 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (0 <= retval_2) ”
.

Definition eval_range_partial_solve_wit_19_pure_split_goal_2 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval_2 <= INT_MAX)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (ops_size_pre >= INT_MIN)) (PreH10 : (idx >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : (retval_2 >= INT_MIN)) (PreH15 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH16 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH17 : (idx <> (-1))) (PreH18 : (i >= hi_pre)) (PreH19 : (lo_pre <= i)) (PreH20 : (i <= hi_pre)) (PreH21 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH22 : (lo_pre <= idx)) (PreH23 : (idx < i)) (PreH24 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH25 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH26 : (ops_size_pre = (Zlength (ops_l)))) (PreH27 : (nums_size_pre = (Zlength (nums_l)))) (PreH28 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH29 : (0 <= lo_pre)) (PreH30 : (lo_pre < hi_pre)) (PreH31 : (hi_pre < nums_size_pre)) (PreH32 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (retval_2 < INT_MAX) ”
.

Definition eval_range_partial_solve_wit_19_pure_split_goal_3 := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (nums_size_pre <= INT_MAX)) (PreH2 : (ops_size_pre <= INT_MAX)) (PreH3 : (idx <= INT_MAX)) (PreH4 : (hi_pre <= INT_MAX)) (PreH5 : (lo_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (retval_2 <= INT_MAX)) (PreH8 : (nums_size_pre >= INT_MIN)) (PreH9 : (ops_size_pre >= INT_MIN)) (PreH10 : (idx >= INT_MIN)) (PreH11 : (hi_pre >= INT_MIN)) (PreH12 : (lo_pre >= INT_MIN)) (PreH13 : (retval >= INT_MIN)) (PreH14 : (retval_2 >= INT_MIN)) (PreH15 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH16 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH17 : (idx <> (-1))) (PreH18 : (i >= hi_pre)) (PreH19 : (lo_pre <= i)) (PreH20 : (i <= hi_pre)) (PreH21 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH22 : (lo_pre <= idx)) (PreH23 : (idx < i)) (PreH24 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH25 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH26 : (ops_size_pre = (Zlength (ops_l)))) (PreH27 : (nums_size_pre = (Zlength (nums_l)))) (PreH28 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH29 : (0 <= lo_pre)) (PreH30 : (lo_pre < hi_pre)) (PreH31 : (hi_pre < nums_size_pre)) (PreH32 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
  **  ((( &( "right" ) )) # Int  |-> retval_2)
  **  ((( &( "left" ) )) # Int  |-> retval)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ops_size" ) )) # Int  |-> ops_size_pre)
  **  ((( &( "nums_size" ) )) # Int  |-> nums_size_pre)
  **  ((( &( "ops" ) )) # Ptr  |-> ops_pre)
  **  ((( &( "nums" ) )) # Ptr  |-> nums_pre)
|--
  “ (pow_prefix_safe_160 retval retval_2 ) ”
.

Definition eval_range_partial_solve_wit_19_aux := 
forall (hi_pre: Z) (lo_pre: Z) (nums_size_pre: Z) (nums_pre: Z) (ops_size_pre: Z) (ops_pre: Z) (nums_l: (@list Z)) (ops_l: (@list Z)) (idx: Z) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre)))) (PreH2 : (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx)))) (PreH3 : (idx <> (-1))) (PreH4 : (i >= hi_pre)) (PreH5 : (lo_pre <= i)) (PreH6 : (i <= hi_pre)) (PreH7 : (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i)))) (PreH8 : (lo_pre <= idx)) (PreH9 : (idx < i)) (PreH10 : ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH11 : ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1))) (PreH12 : (ops_size_pre = (Zlength (ops_l)))) (PreH13 : (nums_size_pre = (Zlength (nums_l)))) (PreH14 : ((ops_size_pre + 1 ) = nums_size_pre)) (PreH15 : (0 <= lo_pre)) (PreH16 : (lo_pre < hi_pre)) (PreH17 : (hi_pre < nums_size_pre)) (PreH18 : (eval_range_safe_160 ops_l nums_l lo_pre hi_pre )) ,
  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
|--
  “ (pow_prefix_safe_160 retval retval_2 ) ” 
  &&  “ (retval_2 < INT_MAX) ” 
  &&  “ (0 <= retval_2) ” 
  &&  “ (retval_2 = (eval_range_160 (ops_l) (nums_l) ((idx + 1 )) (hi_pre))) ” 
  &&  “ (retval = (eval_range_160 (ops_l) (nums_l) (lo_pre) (idx))) ” 
  &&  “ (idx <> (-1)) ” 
  &&  “ (i >= hi_pre) ” 
  &&  “ (lo_pre <= i) ” 
  &&  “ (i <= hi_pre) ” 
  &&  “ (idx = (find_pow_left_prefix_160 (ops_l) (lo_pre) (i))) ” 
  &&  “ (lo_pre <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ ((find_addsub_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ ((find_muldiv_prefix_160 (ops_l) (lo_pre) (hi_pre)) = (-1)) ” 
  &&  “ (ops_size_pre = (Zlength (ops_l))) ” 
  &&  “ (nums_size_pre = (Zlength (nums_l))) ” 
  &&  “ ((ops_size_pre + 1 ) = nums_size_pre) ” 
  &&  “ (0 <= lo_pre) ” 
  &&  “ (lo_pre < hi_pre) ” 
  &&  “ (hi_pre < nums_size_pre) ” 
  &&  “ (eval_range_safe_160 ops_l nums_l lo_pre hi_pre ) ”
  &&  (IntArray.full ops_pre ops_size_pre ops_l )
  **  (IntArray.full nums_pre nums_size_pre nums_l )
.

Definition eval_range_partial_solve_wit_19 := eval_range_partial_solve_wit_19_pure -> eval_range_partial_solve_wit_19_aux.

(*----- Function do_algebra -----*)

Definition do_algebra_safety_wit_1 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (0 < operato_size_pre)) (PreH2 : (operato_size_pre < INT_MAX)) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (operand_size_pre < INT_MAX)) (PreH5 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH6 : (problem_160_pre_z rows operands )) (PreH7 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "cur_op" ) )) # Ptr  |->_)
  **  ((( &( "ops" ) )) # Ptr  |->_)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition do_algebra_safety_wit_2 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 < operato_size_pre)) (PreH3 : (operato_size_pre < INT_MAX)) (PreH4 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.undef_full retval operato_size_pre )
  **  ((( &( "cur_op" ) )) # Ptr  |-> 0)
  **  ((( &( "ops" ) )) # Ptr  |-> retval)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition do_algebra_safety_wit_3 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.undef_full retval operato_size_pre )
  **  ((( &( "cur_op" ) )) # Ptr  |-> 0)
  **  ((( &( "ops" ) )) # Ptr  |-> retval)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ False ”
.

Definition do_algebra_safety_wit_4 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (IntArray.undef_full retval operato_size_pre )
  **  ((( &( "cur_op" ) )) # Ptr  |-> 0)
  **  ((( &( "ops" ) )) # Ptr  |-> retval)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition do_algebra_safety_wit_5 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.seg ops 0 (i + 1 ) (app (ops_l) ((cons (retval) ((@nil Z))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (IntArray.undef_seg ops (i + 1 ) operato_size_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition do_algebra_safety_wit_6 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (ops <> 0)) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ ((operand_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (operand_size_pre - 1 )) ”
.

Definition do_algebra_safety_wit_7 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (ops <> 0)) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition do_algebra_safety_wit_8 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (ops <> 0)) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition do_algebra_entail_wit_1 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.undef_full retval operato_size_pre )
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  EX (ops_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= operato_size_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) (0) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg retval 0 0 ops_l )
  **  (IntArray.undef_seg retval 0 operato_size_pre )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  TT && emp 
|--
  “ ((@nil Z) = (sublist (0) (0) ((operator_codes_160 (rows))))) ”
  &&  emp
).

Definition do_algebra_entail_wit_1_split_goal_1 := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  TT && emp 
|--
  “ ((@nil Z) = (sublist (0) (0) ((operator_codes_160 (rows))))) ”
.

Definition do_algebra_entail_wit_2 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (ops: Z) (i: Z) (PreH1 : (i < operato_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l_2 )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  EX (row_ptr: Z)  (ops_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < operato_size_pre) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) (i) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (ops: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < operato_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (problem_160_pre_z rows operands )) (PreH13 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
).

Definition do_algebra_entail_wit_2_split_goal_1 := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (ops: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < operato_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (problem_160_pre_z rows operands )) (PreH13 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition do_algebra_entail_wit_2_split_goal_spatial := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (ops: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < operato_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (problem_160_pre_z rows operands )) (PreH13 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
.

Definition do_algebra_entail_wit_3 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (PreH1 : (0 <= i)) (PreH2 : (i < operato_size_pre)) (PreH3 : (ops <> 0)) (PreH4 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH5 : (0 < operato_size_pre)) (PreH6 : (operato_size_pre < INT_MAX)) (PreH7 : (operand_size_pre < INT_MAX)) (PreH8 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH9 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH10 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l_2 )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  EX (ops_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < operato_size_pre) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) (i) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH12 : (problem_160_pre_z rows operands )) (PreH13 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition do_algebra_entail_wit_3_split_goal_spatial := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (PreH1 : (0 <= (Zlength ((Znth (i) (rows) ((@nil Z))))))) (PreH2 : (0 <= i)) (PreH3 : (i < operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH12 : (problem_160_pre_z rows operands )) (PreH13 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr (Zlength ((Znth (i) (rows) ((@nil Z))))) (Znth (i) (rows) ((@nil Z))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition do_algebra_entail_wit_4 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.seg ops 0 (i + 1 ) (app (ops_l_2) ((cons (retval) ((@nil Z))))) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (IntArray.undef_seg ops (i + 1 ) operato_size_pre )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  EX (ops_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= operato_size_pre) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) ((i + 1 )) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 (i + 1 ) ops_l )
  **  (IntArray.undef_seg ops (i + 1 ) operato_size_pre )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((app (ops_l_2) ((cons (retval) ((@nil Z))))) = (sublist (0) ((i + 1 )) ((operator_codes_160 (rows))))) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
).

Definition do_algebra_entail_wit_4_split_goal_1 := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((app (ops_l_2) ((cons (retval) ((@nil Z))))) = (sublist (0) ((i + 1 )) ((operator_codes_160 (rows))))) ”
.

Definition do_algebra_entail_wit_4_split_goal_spatial := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l_2: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l_2 = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full operato_pre operato_size_pre rows )
.

Definition do_algebra_entail_wit_5 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (ops: Z) (i: Z) (PreH1 : (i >= operato_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (ops: Z) (i: Z) (PreH1 : (i >= operato_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.seg ops 0 i ops_l )
|--
  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
).

Definition do_algebra_entail_wit_5_split_goal_spatial := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (ops: Z) (i: Z) (PreH1 : (i >= operato_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= operato_size_pre)) (PreH4 : (ops <> 0)) (PreH5 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH6 : (0 < operato_size_pre)) (PreH7 : (operato_size_pre < INT_MAX)) (PreH8 : (operand_size_pre < INT_MAX)) (PreH9 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.seg ops 0 i ops_l )
|--
  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
.

Definition do_algebra_entail_wit_6 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (retval: Z) (PreH1 : (retval = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH2 : (ops <> 0)) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (0 < operato_size_pre)) (PreH5 : (operato_size_pre < INT_MAX)) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
|--
  “ (ops <> 0) ” 
  &&  “ (retval = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 )))) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
.

Definition do_algebra_entail_wit_7 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (ans: Z) (PreH1 : (ops <> 0)) (PreH2 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (0 < operato_size_pre)) (PreH5 : (operato_size_pre < INT_MAX)) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 )))) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
.

Definition do_algebra_return_wit_1 := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ans: Z) (PreH1 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (problem_160_spec_z rows operands ans ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
) \/
(
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ans: Z) (PreH1 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  TT && emp 
|--
  “ (problem_160_spec_z rows operands ans ) ”
  &&  emp
).

Definition do_algebra_return_wit_1_split_goal_1 := 
forall (operand_size_pre: Z) (operato_size_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ans: Z) (PreH1 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  TT && emp 
|--
  “ (problem_160_spec_z rows operands ans ) ”
.

Definition do_algebra_partial_solve_wit_1_pure := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (0 < operato_size_pre)) (PreH2 : (operato_size_pre < INT_MAX)) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (operand_size_pre < INT_MAX)) (PreH5 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH6 : (problem_160_pre_z rows operands )) (PreH7 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "cur_op" ) )) # Ptr  |-> 0)
  **  ((( &( "ops" ) )) # Ptr  |->_)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (operato_size_pre >= 0) ” 
  &&  “ (operato_size_pre < INT_MAX) ”
.

Definition do_algebra_partial_solve_wit_1_aux := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (PreH1 : (0 < operato_size_pre)) (PreH2 : (operato_size_pre < INT_MAX)) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (operand_size_pre < INT_MAX)) (PreH5 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH6 : (problem_160_pre_z rows operands )) (PreH7 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
|--
  “ (operato_size_pre >= 0) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
.

Definition do_algebra_partial_solve_wit_1 := do_algebra_partial_solve_wit_1_pure -> do_algebra_partial_solve_wit_1_aux.

Definition do_algebra_partial_solve_wit_2_pure := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (PreH1 : (0 <= i)) (PreH2 : (i < operato_size_pre)) (PreH3 : (ops <> 0)) (PreH4 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH5 : (0 < operato_size_pre)) (PreH6 : (operato_size_pre < INT_MAX)) (PreH7 : (operand_size_pre < INT_MAX)) (PreH8 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH9 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH10 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition do_algebra_partial_solve_wit_2_aux := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (PreH1 : (0 <= i)) (PreH2 : (i < operato_size_pre)) (PreH3 : (ops <> 0)) (PreH4 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH5 : (0 < operato_size_pre)) (PreH6 : (operato_size_pre < INT_MAX)) (PreH7 : (operand_size_pre < INT_MAX)) (PreH8 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH9 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH10 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < operato_size_pre) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) (i) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (store_string row_ptr (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
.

Definition do_algebra_partial_solve_wit_2 := do_algebra_partial_solve_wit_2_pure -> do_algebra_partial_solve_wit_2_aux.

Definition do_algebra_partial_solve_wit_3 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops_l: (@list Z)) (row_ptr: Z) (i: Z) (ops: Z) (retval: Z) (PreH1 : (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < operato_size_pre)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (ops_l = (sublist (0) (i) ((operator_codes_160 (rows)))))) (PreH11 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH12 : (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : (problem_160_pre_z rows operands )) (PreH14 : (do_algebra_safe_160 rows operands )) ,
  (store_string row_ptr (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
  **  (IntArray.undef_seg ops i operato_size_pre )
|--
  “ (retval = (operator_code_payload_160 ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < operato_size_pre) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (ops_l = (sublist (0) (i) ((operator_codes_160 (rows))))) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (operator_payload_valid_160 (row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (((ops + (i * sizeof(INT) ) )) # Int  |->_)
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_160 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (IntArray.undef_seg ops (i + 1 ) operato_size_pre )
  **  (CharPtrArray2.missing_i operato_pre operato_size_pre i row_ptr rows )
  **  (((operato_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.seg ops 0 i ops_l )
.

Definition do_algebra_partial_solve_wit_4_pure := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (ops <> 0)) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ ((operato_size_pre + 1 ) = operand_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (operand_size_pre - 1 )) ” 
  &&  “ ((operand_size_pre - 1 ) < operand_size_pre) ” 
  &&  “ (eval_range_safe_160 (operator_codes_160 (rows)) operands 0 (operand_size_pre - 1 ) ) ” 
  &&  “ (operand_size_pre = (Zlength (operands))) ” 
  &&  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ”
) \/
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (operato_size_pre >= INT_MIN)) (PreH4 : (operand_size_pre >= INT_MIN)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ” 
  &&  “ (operand_size_pre = (Zlength (operands))) ” 
  &&  “ (eval_range_safe_160 (operator_codes_160 (rows)) operands 0 (operand_size_pre - 1 ) ) ”
).

Definition do_algebra_partial_solve_wit_4_pure_split_goal_1 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (operato_size_pre >= INT_MIN)) (PreH4 : (operand_size_pre >= INT_MIN)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ”
.

Definition do_algebra_partial_solve_wit_4_pure_split_goal_2 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (operato_size_pre >= INT_MIN)) (PreH4 : (operand_size_pre >= INT_MIN)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (operand_size_pre = (Zlength (operands))) ”
.

Definition do_algebra_partial_solve_wit_4_pure_split_goal_3 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (operato_size_pre >= INT_MIN)) (PreH4 : (operand_size_pre >= INT_MIN)) (PreH5 : (ops <> 0)) (PreH6 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH7 : (0 < operato_size_pre)) (PreH8 : (operato_size_pre < INT_MAX)) (PreH9 : (operand_size_pre < INT_MAX)) (PreH10 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH11 : (problem_160_pre_z rows operands )) (PreH12 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ans" ) )) # Int  |->_)
  **  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (eval_range_safe_160 (operator_codes_160 (rows)) operands 0 (operand_size_pre - 1 ) ) ”
.

Definition do_algebra_partial_solve_wit_4_aux := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (PreH1 : (ops <> 0)) (PreH2 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH3 : (0 < operato_size_pre)) (PreH4 : (operato_size_pre < INT_MAX)) (PreH5 : (operand_size_pre < INT_MAX)) (PreH6 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH7 : (problem_160_pre_z rows operands )) (PreH8 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ ((operato_size_pre + 1 ) = operand_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (operand_size_pre - 1 )) ” 
  &&  “ ((operand_size_pre - 1 ) < operand_size_pre) ” 
  &&  “ (eval_range_safe_160 (operator_codes_160 (rows)) operands 0 (operand_size_pre - 1 ) ) ” 
  &&  “ (operand_size_pre = (Zlength (operands))) ” 
  &&  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
.

Definition do_algebra_partial_solve_wit_4 := do_algebra_partial_solve_wit_4_pure -> do_algebra_partial_solve_wit_4_aux.

Definition do_algebra_partial_solve_wit_5_pure := 
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (ans: Z) (cur_op: Z) (PreH1 : (ops <> 0)) (PreH2 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (0 < operato_size_pre)) (PreH5 : (operato_size_pre < INT_MAX)) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (ops <> 0) ” 
  &&  “ (0 <= operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ”
) \/
(
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (ans: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (operato_size_pre >= INT_MIN)) (PreH5 : (operand_size_pre >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (ops <> 0)) (PreH8 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH9 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH10 : (0 < operato_size_pre)) (PreH11 : (operato_size_pre < INT_MAX)) (PreH12 : (operand_size_pre < INT_MAX)) (PreH13 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH14 : (problem_160_pre_z rows operands )) (PreH15 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ”
).

Definition do_algebra_partial_solve_wit_5_pure_split_goal_1 := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (ans: Z) (cur_op: Z) (PreH1 : (operato_size_pre <= INT_MAX)) (PreH2 : (operand_size_pre <= INT_MAX)) (PreH3 : (ans <= INT_MAX)) (PreH4 : (operato_size_pre >= INT_MIN)) (PreH5 : (operand_size_pre >= INT_MIN)) (PreH6 : (ans >= INT_MIN)) (PreH7 : (ops <> 0)) (PreH8 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH9 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH10 : (0 < operato_size_pre)) (PreH11 : (operato_size_pre < INT_MAX)) (PreH12 : (operand_size_pre < INT_MAX)) (PreH13 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH14 : (problem_160_pre_z rows operands )) (PreH15 : (do_algebra_safe_160 rows operands )) ,
  ((( &( "ops" ) )) # Ptr  |-> ops)
  **  ((( &( "ans" ) )) # Int  |-> ans)
  **  ((( &( "operand_size" ) )) # Int  |-> operand_size_pre)
  **  ((( &( "operato_size" ) )) # Int  |-> operato_size_pre)
  **  ((( &( "operand" ) )) # Ptr  |-> operand_pre)
  **  ((( &( "operato" ) )) # Ptr  |-> operato_pre)
  **  ((( &( "cur_op" ) )) # Ptr  |-> cur_op)
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ”
.

Definition do_algebra_partial_solve_wit_5_aux := 
forall (operand_size_pre: Z) (operand_pre: Z) (operato_size_pre: Z) (operato_pre: Z) (operands: (@list Z)) (rows: (@list (@list Z))) (ops: Z) (ans: Z) (PreH1 : (ops <> 0)) (PreH2 : (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 ))))) (PreH3 : (operand_size_pre = (operato_size_pre + 1 ))) (PreH4 : (0 < operato_size_pre)) (PreH5 : (operato_size_pre < INT_MAX)) (PreH6 : (operand_size_pre < INT_MAX)) (PreH7 : (operator_rows_well_formed_160 rows operato_size_pre )) (PreH8 : (problem_160_pre_z rows operands )) (PreH9 : (do_algebra_safe_160 rows operands )) ,
  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
  **  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
|--
  “ (ops <> 0) ” 
  &&  “ (0 <= operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operato_size_pre = (Zlength ((operator_codes_160 (rows))))) ” 
  &&  “ (ops <> 0) ” 
  &&  “ (ans = (eval_range_160 ((operator_codes_160 (rows))) (operands) (0) ((operand_size_pre - 1 )))) ” 
  &&  “ (operand_size_pre = (operato_size_pre + 1 )) ” 
  &&  “ (0 < operato_size_pre) ” 
  &&  “ (operato_size_pre < INT_MAX) ” 
  &&  “ (operand_size_pre < INT_MAX) ” 
  &&  “ (operator_rows_well_formed_160 rows operato_size_pre ) ” 
  &&  “ (problem_160_pre_z rows operands ) ” 
  &&  “ (do_algebra_safe_160 rows operands ) ”
  &&  (IntArray.full ops operato_size_pre (operator_codes_160 (rows)) )
  **  (CharPtrArray2.full operato_pre operato_size_pre rows )
  **  (IntArray.full operand_pre operand_size_pre operands )
.

Definition do_algebra_partial_solve_wit_5 := do_algebra_partial_solve_wit_5_pure -> do_algebra_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_operator_code_safety_wit_1 : operator_code_safety_wit_1.
Axiom proof_of_operator_code_safety_wit_2 : operator_code_safety_wit_2.
Axiom proof_of_operator_code_safety_wit_3 : operator_code_safety_wit_3.
Axiom proof_of_operator_code_safety_wit_4 : operator_code_safety_wit_4.
Axiom proof_of_operator_code_safety_wit_5 : operator_code_safety_wit_5.
Axiom proof_of_operator_code_safety_wit_6 : operator_code_safety_wit_6.
Axiom proof_of_operator_code_safety_wit_7 : operator_code_safety_wit_7.
Axiom proof_of_operator_code_safety_wit_8 : operator_code_safety_wit_8.
Axiom proof_of_operator_code_safety_wit_9 : operator_code_safety_wit_9.
Axiom proof_of_operator_code_safety_wit_10 : operator_code_safety_wit_10.
Axiom proof_of_operator_code_safety_wit_11 : operator_code_safety_wit_11.
Axiom proof_of_operator_code_safety_wit_12 : operator_code_safety_wit_12.
Axiom proof_of_operator_code_safety_wit_13 : operator_code_safety_wit_13.
Axiom proof_of_operator_code_return_wit_1 : operator_code_return_wit_1.
Axiom proof_of_operator_code_return_wit_2 : operator_code_return_wit_2.
Axiom proof_of_operator_code_return_wit_3 : operator_code_return_wit_3.
Axiom proof_of_operator_code_return_wit_4 : operator_code_return_wit_4.
Axiom proof_of_operator_code_return_wit_5 : operator_code_return_wit_5.
Axiom proof_of_int_pow_safety_wit_1 : int_pow_safety_wit_1.
Axiom proof_of_int_pow_safety_wit_2 : int_pow_safety_wit_2.
Axiom proof_of_int_pow_safety_wit_3 : int_pow_safety_wit_3.
Axiom proof_of_int_pow_safety_wit_4 : int_pow_safety_wit_4.
Axiom proof_of_int_pow_entail_wit_1 : int_pow_entail_wit_1.
Axiom proof_of_int_pow_entail_wit_2 : int_pow_entail_wit_2.
Axiom proof_of_int_pow_return_wit_1 : int_pow_return_wit_1.
Axiom proof_of_eval_range_safety_wit_1 : eval_range_safety_wit_1.
Axiom proof_of_eval_range_safety_wit_2 : eval_range_safety_wit_2.
Axiom proof_of_eval_range_safety_wit_3 : eval_range_safety_wit_3.
Axiom proof_of_eval_range_safety_wit_4 : eval_range_safety_wit_4.
Axiom proof_of_eval_range_safety_wit_5 : eval_range_safety_wit_5.
Axiom proof_of_eval_range_safety_wit_6 : eval_range_safety_wit_6.
Axiom proof_of_eval_range_safety_wit_7 : eval_range_safety_wit_7.
Axiom proof_of_eval_range_safety_wit_8 : eval_range_safety_wit_8.
Axiom proof_of_eval_range_safety_wit_9 : eval_range_safety_wit_9.
Axiom proof_of_eval_range_safety_wit_10 : eval_range_safety_wit_10.
Axiom proof_of_eval_range_safety_wit_11 : eval_range_safety_wit_11.
Axiom proof_of_eval_range_safety_wit_12 : eval_range_safety_wit_12.
Axiom proof_of_eval_range_safety_wit_13 : eval_range_safety_wit_13.
Axiom proof_of_eval_range_safety_wit_14 : eval_range_safety_wit_14.
Axiom proof_of_eval_range_safety_wit_15 : eval_range_safety_wit_15.
Axiom proof_of_eval_range_safety_wit_16 : eval_range_safety_wit_16.
Axiom proof_of_eval_range_safety_wit_17 : eval_range_safety_wit_17.
Axiom proof_of_eval_range_safety_wit_18 : eval_range_safety_wit_18.
Axiom proof_of_eval_range_safety_wit_19 : eval_range_safety_wit_19.
Axiom proof_of_eval_range_safety_wit_20 : eval_range_safety_wit_20.
Axiom proof_of_eval_range_safety_wit_21 : eval_range_safety_wit_21.
Axiom proof_of_eval_range_safety_wit_22 : eval_range_safety_wit_22.
Axiom proof_of_eval_range_safety_wit_23 : eval_range_safety_wit_23.
Axiom proof_of_eval_range_safety_wit_24 : eval_range_safety_wit_24.
Axiom proof_of_eval_range_safety_wit_25 : eval_range_safety_wit_25.
Axiom proof_of_eval_range_safety_wit_26 : eval_range_safety_wit_26.
Axiom proof_of_eval_range_safety_wit_27 : eval_range_safety_wit_27.
Axiom proof_of_eval_range_safety_wit_28 : eval_range_safety_wit_28.
Axiom proof_of_eval_range_safety_wit_29 : eval_range_safety_wit_29.
Axiom proof_of_eval_range_safety_wit_30 : eval_range_safety_wit_30.
Axiom proof_of_eval_range_safety_wit_31 : eval_range_safety_wit_31.
Axiom proof_of_eval_range_safety_wit_32 : eval_range_safety_wit_32.
Axiom proof_of_eval_range_safety_wit_33 : eval_range_safety_wit_33.
Axiom proof_of_eval_range_safety_wit_34 : eval_range_safety_wit_34.
Axiom proof_of_eval_range_safety_wit_35 : eval_range_safety_wit_35.
Axiom proof_of_eval_range_safety_wit_36 : eval_range_safety_wit_36.
Axiom proof_of_eval_range_safety_wit_37 : eval_range_safety_wit_37.
Axiom proof_of_eval_range_safety_wit_38 : eval_range_safety_wit_38.
Axiom proof_of_eval_range_safety_wit_39 : eval_range_safety_wit_39.
Axiom proof_of_eval_range_safety_wit_40 : eval_range_safety_wit_40.
Axiom proof_of_eval_range_safety_wit_41 : eval_range_safety_wit_41.
Axiom proof_of_eval_range_safety_wit_42 : eval_range_safety_wit_42.
Axiom proof_of_eval_range_safety_wit_43 : eval_range_safety_wit_43.
Axiom proof_of_eval_range_safety_wit_44 : eval_range_safety_wit_44.
Axiom proof_of_eval_range_safety_wit_45 : eval_range_safety_wit_45.
Axiom proof_of_eval_range_safety_wit_46 : eval_range_safety_wit_46.
Axiom proof_of_eval_range_safety_wit_47 : eval_range_safety_wit_47.
Axiom proof_of_eval_range_safety_wit_48 : eval_range_safety_wit_48.
Axiom proof_of_eval_range_safety_wit_49 : eval_range_safety_wit_49.
Axiom proof_of_eval_range_safety_wit_50 : eval_range_safety_wit_50.
Axiom proof_of_eval_range_safety_wit_51 : eval_range_safety_wit_51.
Axiom proof_of_eval_range_safety_wit_52 : eval_range_safety_wit_52.
Axiom proof_of_eval_range_safety_wit_53 : eval_range_safety_wit_53.
Axiom proof_of_eval_range_safety_wit_54 : eval_range_safety_wit_54.
Axiom proof_of_eval_range_safety_wit_55 : eval_range_safety_wit_55.
Axiom proof_of_eval_range_safety_wit_56 : eval_range_safety_wit_56.
Axiom proof_of_eval_range_safety_wit_57 : eval_range_safety_wit_57.
Axiom proof_of_eval_range_safety_wit_58 : eval_range_safety_wit_58.
Axiom proof_of_eval_range_safety_wit_59 : eval_range_safety_wit_59.
Axiom proof_of_eval_range_safety_wit_60 : eval_range_safety_wit_60.
Axiom proof_of_eval_range_safety_wit_61 : eval_range_safety_wit_61.
Axiom proof_of_eval_range_safety_wit_62 : eval_range_safety_wit_62.
Axiom proof_of_eval_range_safety_wit_63 : eval_range_safety_wit_63.
Axiom proof_of_eval_range_safety_wit_64 : eval_range_safety_wit_64.
Axiom proof_of_eval_range_safety_wit_65 : eval_range_safety_wit_65.
Axiom proof_of_eval_range_safety_wit_66 : eval_range_safety_wit_66.
Axiom proof_of_eval_range_safety_wit_67 : eval_range_safety_wit_67.
Axiom proof_of_eval_range_entail_wit_1 : eval_range_entail_wit_1.
Axiom proof_of_eval_range_entail_wit_2_1 : eval_range_entail_wit_2_1.
Axiom proof_of_eval_range_entail_wit_2_2 : eval_range_entail_wit_2_2.
Axiom proof_of_eval_range_entail_wit_2_3 : eval_range_entail_wit_2_3.
Axiom proof_of_eval_range_entail_wit_2_4 : eval_range_entail_wit_2_4.
Axiom proof_of_eval_range_entail_wit_2_5 : eval_range_entail_wit_2_5.
Axiom proof_of_eval_range_entail_wit_2_6 : eval_range_entail_wit_2_6.
Axiom proof_of_eval_range_entail_wit_3 : eval_range_entail_wit_3.
Axiom proof_of_eval_range_entail_wit_4 : eval_range_entail_wit_4.
Axiom proof_of_eval_range_entail_wit_5_1 : eval_range_entail_wit_5_1.
Axiom proof_of_eval_range_entail_wit_5_2 : eval_range_entail_wit_5_2.
Axiom proof_of_eval_range_entail_wit_5_3 : eval_range_entail_wit_5_3.
Axiom proof_of_eval_range_entail_wit_5_4 : eval_range_entail_wit_5_4.
Axiom proof_of_eval_range_entail_wit_5_5 : eval_range_entail_wit_5_5.
Axiom proof_of_eval_range_entail_wit_5_6 : eval_range_entail_wit_5_6.
Axiom proof_of_eval_range_entail_wit_6 : eval_range_entail_wit_6.
Axiom proof_of_eval_range_entail_wit_7 : eval_range_entail_wit_7.
Axiom proof_of_eval_range_entail_wit_8_1 : eval_range_entail_wit_8_1.
Axiom proof_of_eval_range_entail_wit_8_2 : eval_range_entail_wit_8_2.
Axiom proof_of_eval_range_entail_wit_8_3 : eval_range_entail_wit_8_3.
Axiom proof_of_eval_range_return_wit_1 : eval_range_return_wit_1.
Axiom proof_of_eval_range_return_wit_2 : eval_range_return_wit_2.
Axiom proof_of_eval_range_return_wit_3 : eval_range_return_wit_3.
Axiom proof_of_eval_range_return_wit_4 : eval_range_return_wit_4.
Axiom proof_of_eval_range_return_wit_5 : eval_range_return_wit_5.
Axiom proof_of_eval_range_return_wit_6 : eval_range_return_wit_6.
Axiom proof_of_eval_range_return_wit_7 : eval_range_return_wit_7.
Axiom proof_of_eval_range_partial_solve_wit_1 : eval_range_partial_solve_wit_1.
Axiom proof_of_eval_range_partial_solve_wit_2 : eval_range_partial_solve_wit_2.
Axiom proof_of_eval_range_partial_solve_wit_3 : eval_range_partial_solve_wit_3.
Axiom proof_of_eval_range_partial_solve_wit_4 : eval_range_partial_solve_wit_4.
Axiom proof_of_eval_range_partial_solve_wit_5 : eval_range_partial_solve_wit_5.
Axiom proof_of_eval_range_partial_solve_wit_6_pure : eval_range_partial_solve_wit_6_pure.
Axiom proof_of_eval_range_partial_solve_wit_6 : eval_range_partial_solve_wit_6.
Axiom proof_of_eval_range_partial_solve_wit_7_pure : eval_range_partial_solve_wit_7_pure.
Axiom proof_of_eval_range_partial_solve_wit_7 : eval_range_partial_solve_wit_7.
Axiom proof_of_eval_range_partial_solve_wit_8 : eval_range_partial_solve_wit_8.
Axiom proof_of_eval_range_partial_solve_wit_9 : eval_range_partial_solve_wit_9.
Axiom proof_of_eval_range_partial_solve_wit_10 : eval_range_partial_solve_wit_10.
Axiom proof_of_eval_range_partial_solve_wit_11 : eval_range_partial_solve_wit_11.
Axiom proof_of_eval_range_partial_solve_wit_12 : eval_range_partial_solve_wit_12.
Axiom proof_of_eval_range_partial_solve_wit_13_pure : eval_range_partial_solve_wit_13_pure.
Axiom proof_of_eval_range_partial_solve_wit_13 : eval_range_partial_solve_wit_13.
Axiom proof_of_eval_range_partial_solve_wit_14_pure : eval_range_partial_solve_wit_14_pure.
Axiom proof_of_eval_range_partial_solve_wit_14 : eval_range_partial_solve_wit_14.
Axiom proof_of_eval_range_partial_solve_wit_15 : eval_range_partial_solve_wit_15.
Axiom proof_of_eval_range_partial_solve_wit_16 : eval_range_partial_solve_wit_16.
Axiom proof_of_eval_range_partial_solve_wit_17_pure : eval_range_partial_solve_wit_17_pure.
Axiom proof_of_eval_range_partial_solve_wit_17 : eval_range_partial_solve_wit_17.
Axiom proof_of_eval_range_partial_solve_wit_18_pure : eval_range_partial_solve_wit_18_pure.
Axiom proof_of_eval_range_partial_solve_wit_18 : eval_range_partial_solve_wit_18.
Axiom proof_of_eval_range_partial_solve_wit_19_pure : eval_range_partial_solve_wit_19_pure.
Axiom proof_of_eval_range_partial_solve_wit_19 : eval_range_partial_solve_wit_19.
Axiom proof_of_do_algebra_safety_wit_1 : do_algebra_safety_wit_1.
Axiom proof_of_do_algebra_safety_wit_2 : do_algebra_safety_wit_2.
Axiom proof_of_do_algebra_safety_wit_3 : do_algebra_safety_wit_3.
Axiom proof_of_do_algebra_safety_wit_4 : do_algebra_safety_wit_4.
Axiom proof_of_do_algebra_safety_wit_5 : do_algebra_safety_wit_5.
Axiom proof_of_do_algebra_safety_wit_6 : do_algebra_safety_wit_6.
Axiom proof_of_do_algebra_safety_wit_7 : do_algebra_safety_wit_7.
Axiom proof_of_do_algebra_safety_wit_8 : do_algebra_safety_wit_8.
Axiom proof_of_do_algebra_entail_wit_1 : do_algebra_entail_wit_1.
Axiom proof_of_do_algebra_entail_wit_2 : do_algebra_entail_wit_2.
Axiom proof_of_do_algebra_entail_wit_3 : do_algebra_entail_wit_3.
Axiom proof_of_do_algebra_entail_wit_4 : do_algebra_entail_wit_4.
Axiom proof_of_do_algebra_entail_wit_5 : do_algebra_entail_wit_5.
Axiom proof_of_do_algebra_entail_wit_6 : do_algebra_entail_wit_6.
Axiom proof_of_do_algebra_entail_wit_7 : do_algebra_entail_wit_7.
Axiom proof_of_do_algebra_return_wit_1 : do_algebra_return_wit_1.
Axiom proof_of_do_algebra_partial_solve_wit_1_pure : do_algebra_partial_solve_wit_1_pure.
Axiom proof_of_do_algebra_partial_solve_wit_1 : do_algebra_partial_solve_wit_1.
Axiom proof_of_do_algebra_partial_solve_wit_2_pure : do_algebra_partial_solve_wit_2_pure.
Axiom proof_of_do_algebra_partial_solve_wit_2 : do_algebra_partial_solve_wit_2.
Axiom proof_of_do_algebra_partial_solve_wit_3 : do_algebra_partial_solve_wit_3.
Axiom proof_of_do_algebra_partial_solve_wit_4_pure : do_algebra_partial_solve_wit_4_pure.
Axiom proof_of_do_algebra_partial_solve_wit_4 : do_algebra_partial_solve_wit_4.
Axiom proof_of_do_algebra_partial_solve_wit_5_pure : do_algebra_partial_solve_wit_5_pure.
Axiom proof_of_do_algebra_partial_solve_wit_5 : do_algebra_partial_solve_wit_5.

End VC_Correct.
