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
Require Import p111_histogram.
Local Open Scope sac.
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

(*----- Function histogram -----*)

Definition histogram_safety_wit_1 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : ((string_length (input)) < INT_MAX)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH6 : (problem_111_pre_z input )) ,
  ((( &( "max" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_2 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : ((string_length (input)) < INT_MAX)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH6 : (problem_111_pre_z input )) ,
  ((( &( "keys" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_3 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH7 : (problem_111_pre_z input )) ,
  ((( &( "values" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_4 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_5 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  ((( &( "size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 256 )
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_6 := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 256 )
  **  ((( &( "values" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_7 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 256)) (PreH3 : (size = 0)) (PreH4 : (max = 0)) (PreH5 : (0 <= (string_length (input)))) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : (problem_111_pre_z input )) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH9 : (valid_string input )) (PreH10 : (out <> 0)) (PreH11 : (keys <> 0)) (PreH12 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (IntArray.undef_seg ( &( "count" ) ) i 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_8 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (i < 256)) (PreH2 : (0 <= i)) (PreH3 : (i <= 256)) (PreH4 : (size = 0)) (PreH5 : (max = 0)) (PreH6 : (0 <= (string_length (input)))) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (problem_111_pre_z input )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH10 : (valid_string input )) (PreH11 : (out <> 0)) (PreH12 : (keys <> 0)) (PreH13 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (IntArray.undef_seg ( &( "count" ) ) i 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_9 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (IntArray.seg ( &( "count" ) ) 0 (i + 1 ) (app ((zeros (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_seg ( &( "count" ) ) (i + 1 ) 256 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_10 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (i >= 256)) (PreH2 : (0 <= i)) (PreH3 : (i <= 256)) (PreH4 : (size = 0)) (PreH5 : (max = 0)) (PreH6 : (0 <= (string_length (input)))) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (problem_111_pre_z input )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH10 : (valid_string input )) (PreH11 : (out <> 0)) (PreH12 : (keys <> 0)) (PreH13 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (IntArray.undef_seg ( &( "count" ) ) i 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_11 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= (string_length (input)))) (PreH3 : ((Zlength (counts)) = 256)) (PreH4 : (0 <= max)) (PreH5 : (size = 0)) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH8 : (problem_111_pre_z input )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH10 : (problem_111_scan_state_z input i counts max )) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_12 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= (string_length (input)))) (PreH4 : ((Zlength (counts)) = 256)) (PreH5 : (0 <= max)) (PreH6 : (size = 0)) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (problem_111_scan_state_z input i counts max )) (PreH12 : (valid_string input )) (PreH13 : (out <> 0)) (PreH14 : (keys <> 0)) (PreH15 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition histogram_safety_wit_13 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) <> 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= (string_length (input)))) (PreH5 : ((Zlength (counts)) = 256)) (PreH6 : (0 <= max)) (PreH7 : (size = 0)) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH10 : (problem_111_pre_z input )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH12 : (problem_111_scan_state_z input i counts max )) (PreH13 : (valid_string input )) (PreH14 : (out <> 0)) (PreH15 : (keys <> 0)) (PreH16 : (values <> 0)) ,
  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_14 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= (Znth i (c_string (input)) 0))) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_15 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) ”
) \/
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) ”
).

Definition histogram_safety_wit_15_split_goal_1 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 ) <= INT_MAX) ”
.

Definition histogram_safety_wit_15_split_goal_2 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((INT_MIN) <= ((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) ”
.

Definition histogram_safety_wit_16 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "current" ) )) # Int  |-> (Znth i (c_string (input)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_17 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0))
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_18 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_19 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 > (Znth i (c_string (input)) 0))) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_20 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 256)) (PreH2 : (0 <= (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_21 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= (string_length (input)))) (PreH5 : ((Zlength (counts)) = 256)) (PreH6 : (0 <= max)) (PreH7 : (size = 0)) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH10 : (problem_111_pre_z input )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH12 : (problem_111_scan_state_z input i counts max )) (PreH13 : (valid_string input )) (PreH14 : (out <> 0)) (PreH15 : (keys <> 0)) (PreH16 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition histogram_safety_wit_22 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= (string_length (input)))) (PreH4 : ((Zlength (counts)) = 256)) (PreH5 : (0 <= max)) (PreH6 : (size = 0)) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (problem_111_scan_state_z input i counts max )) (PreH12 : (valid_string input )) (PreH13 : (out <> 0)) (PreH14 : (keys <> 0)) (PreH15 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((( &( "ch" ) )) # Int  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_23 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (i = (string_length (input)))) (PreH2 : (0 <= ch)) (PreH3 : (ch <= 256)) (PreH4 : (0 <= size)) (PreH5 : (size <= ch)) (PreH6 : ((Zlength (counts)) = 256)) (PreH7 : ((Zlength (key_list)) = size)) (PreH8 : ((Zlength (value_list)) = size)) (PreH9 : (problem_111_pre_z input )) (PreH10 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH11 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (out <> 0)) (PreH14 : (keys <> 0)) (PreH15 : (values <> 0)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (256 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 256) ”
.

Definition histogram_safety_wit_24 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : ((Znth ch counts 0) = max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (ch < 256)) (PreH4 : (i = (string_length (input)))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 256)) (PreH7 : (0 <= size)) (PreH8 : (size <= ch)) (PreH9 : ((Zlength (counts)) = 256)) (PreH10 : ((Zlength (key_list)) = size)) (PreH11 : ((Zlength (value_list)) = size)) (PreH12 : (problem_111_pre_z input )) (PreH13 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH14 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition histogram_safety_wit_25 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.seg values 0 (size + 1 ) (app (value_list) ((cons ((Znth ch counts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (size + 1 )) ”
.

Definition histogram_safety_wit_26 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.seg values 0 (size + 1 ) (app (value_list) ((cons ((Znth ch counts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition histogram_safety_wit_27 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.seg values 0 (size + 1 ) (app (value_list) ((cons ((Znth ch counts 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> (size + 1 ))
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  “ ((ch + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ch + 1 )) ”
.

Definition histogram_safety_wit_28 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : ((Znth ch counts 0) <> max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (ch < 256)) (PreH4 : (i = (string_length (input)))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 256)) (PreH7 : (0 <= size)) (PreH8 : (size <= ch)) (PreH9 : ((Zlength (counts)) = 256)) (PreH10 : ((Zlength (key_list)) = size)) (PreH11 : ((Zlength (value_list)) = size)) (PreH12 : (problem_111_pre_z input )) (PreH13 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH14 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ ((ch + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ch + 1 )) ”
.

Definition histogram_safety_wit_29 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "size" ) )) # Int  |-> size)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "keys" ) )) # Ptr  |-> keys)
  **  ((( &( "values" ) )) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ ((ch + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (ch + 1 )) ”
.

Definition histogram_entail_wit_1 := 
(
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 <= (string_length (input))) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> retval_3)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 0 (zeros (0)) )
  **  (IntArray.undef_seg ( &( "count" ) ) 0 256 )
  **  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
) \/
(
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ (0 <= (string_length (input))) ” 
  &&  “ ((zeros (0)) = (@nil Z)) ”
  &&  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
).

Definition histogram_entail_wit_1_split_goal_1 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ (0 <= (string_length (input))) ”
.

Definition histogram_entail_wit_1_split_goal_2 := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  “ ((zeros (0)) = (@nil Z)) ”
.

Definition histogram_entail_wit_1_split_goal_spatial := 
forall (input: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input)) + 1 ))) (PreH5 : (valid_string input )) (PreH6 : ((string_length (input)) < INT_MAX)) (PreH7 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH8 : (problem_111_pre_z input )) ,
  (IntArray.undef_full retval_3 256 )
  **  (CharArray.undef_full retval_2 256 )
|--
  (CharArray.undef_full retval_2 256 )
  **  (IntArray.undef_full retval_3 256 )
.

Definition histogram_entail_wit_2 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (IntArray.seg ( &( "count" ) ) 0 (i + 1 ) (app ((zeros (i))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_seg ( &( "count" ) ) (i + 1 ) 256 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 256) ” 
  &&  “ (size = 0) ” 
  &&  “ (max = 0) ” 
  &&  “ (0 <= (string_length (input))) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 (i + 1 ) (zeros ((i + 1 ))) )
  **  (IntArray.undef_seg ( &( "count" ) ) (i + 1 ) 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((app ((zeros (i))) ((cons (0) ((@nil Z))))) = (zeros ((i + 1 )))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_2_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((app ((zeros (i))) ((cons (0) ((@nil Z))))) = (zeros ((i + 1 )))) ”
.

Definition histogram_entail_wit_2_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i < 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_3 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (i >= 256)) (PreH2 : (0 <= i)) (PreH3 : (i <= 256)) (PreH4 : (size = 0)) (PreH5 : (max = 0)) (PreH6 : (0 <= (string_length (input)))) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (problem_111_pre_z input )) (PreH9 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH10 : (valid_string input )) (PreH11 : (out <> 0)) (PreH12 : (keys <> 0)) (PreH13 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (IntArray.undef_seg ( &( "count" ) ) i 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= 0))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input 0 counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input 0 (zeros (i)) max ) ” 
  &&  “ (((0 <= (Znth (0) ((zeros (i))) (0))) /\ ((Znth (0) ((zeros (i))) (0)) <= 0)) /\ ((0 <= (Znth ((256 - 1 )) ((zeros (i))) (0))) /\ ((Znth ((256 - 1 )) ((zeros (i))) (0)) <= 0))) ” 
  &&  “ ((Zlength ((zeros (i)))) = 256) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_3_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input 0 (zeros (i)) max ) ”
.

Definition histogram_entail_wit_3_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((0 <= (Znth (0) ((zeros (i))) (0))) /\ ((Znth (0) ((zeros (i))) (0)) <= 0)) /\ ((0 <= (Znth ((256 - 1 )) ((zeros (i))) (0))) /\ ((Znth ((256 - 1 )) ((zeros (i))) (0)) <= 0))) ”
.

Definition histogram_entail_wit_3_split_goal_3 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Zlength ((zeros (i)))) = 256) ”
.

Definition histogram_entail_wit_3_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (i >= 256)) (PreH3 : (0 <= i)) (PreH4 : (i <= 256)) (PreH5 : (size = 0)) (PreH6 : (max = 0)) (PreH7 : (0 <= (string_length (input)))) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (valid_string input )) (PreH12 : (out <> 0)) (PreH13 : (keys <> 0)) (PreH14 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_4_1 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0)) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input (i + 1 ) counts (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) ) ” 
  &&  “ (((0 <= (Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 ))) /\ ((0 <= (Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)))) = 256) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_1_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) ) ”
.

Definition histogram_entail_wit_4_1_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((0 <= (Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 ))) /\ ((0 <= (Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 )))) ”
.

Definition histogram_entail_wit_4_1_split_goal_3 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Zlength ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)))) = 256) ”
.

Definition histogram_entail_wit_4_1_split_goal_4 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= (string_length (input))) ”
.

Definition histogram_entail_wit_4_1_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_4_2 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input (i + 1 ) counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) max ) ” 
  &&  “ (((0 <= (Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 ))) /\ ((0 <= (Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 )))) ” 
  &&  “ ((Zlength ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)))) = 256) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_2_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) max ) ”
.

Definition histogram_entail_wit_4_2_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (((0 <= (Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth (0) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 ))) /\ ((0 <= (Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0))) /\ ((Znth ((256 - 1 )) ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2))) (0)) <= (i + 1 )))) ”
.

Definition histogram_entail_wit_4_2_split_goal_3 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Zlength ((replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)))) = 256) ”
.

Definition histogram_entail_wit_4_2_split_goal_4 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= (string_length (input))) ”
.

Definition histogram_entail_wit_4_2_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts_2 0) + 1 )) (counts_2)) 0) <= max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts_2 max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_4_3 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 > (Znth i (c_string (input)) 0))) (PreH2 : ((Znth i (c_string (input)) 0) <> 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts_2)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts_2 max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input (i + 1 ) counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 > (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts_2)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts_2 max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_3_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 > (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts_2)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts_2 max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ”
.

Definition histogram_entail_wit_4_3_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 > (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts_2)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts_2 max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= (string_length (input))) ”
.

Definition histogram_entail_wit_4_3_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : (0 > (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts_2)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts_2 max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_4_4 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) >= 256)) (PreH2 : (0 <= (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts_2)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts_2 max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input (i + 1 ) counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) >= 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts_2)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts_2 max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_4_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) >= 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts_2)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts_2 max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ”
.

Definition histogram_entail_wit_4_4_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) >= 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts_2)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts_2 max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= (string_length (input))) ”
.

Definition histogram_entail_wit_4_4_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) >= 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts_2)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts_2 max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_4_5 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 32)) (PreH2 : ((Znth i (c_string (input)) 0) <> 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= (string_length (input)))) (PreH5 : ((Zlength (counts_2)) = 256)) (PreH6 : (0 <= max)) (PreH7 : (size = 0)) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH10 : (problem_111_pre_z input )) (PreH11 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH12 : (problem_111_scan_state_z input i counts_2 max )) (PreH13 : (valid_string input )) (PreH14 : (out <> 0)) (PreH15 : (keys <> 0)) (PreH16 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (counts: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= (i + 1 )))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input (i + 1 ) counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts_2)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts_2 max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ” 
  &&  “ ((i + 1 ) <= (string_length (input))) ”
  &&  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
).

Definition histogram_entail_wit_4_5_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts_2)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts_2 max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (problem_111_scan_state_z input (i + 1 ) counts_2 max ) ”
.

Definition histogram_entail_wit_4_5_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts_2)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts_2 max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((i + 1 ) <= (string_length (input))) ”
.

Definition histogram_entail_wit_4_5_split_goal_spatial := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 32)) (PreH3 : ((Znth i (c_string (input)) 0) <> 0)) (PreH4 : (0 <= i)) (PreH5 : (i <= (string_length (input)))) (PreH6 : ((Zlength (counts_2)) = 256)) (PreH7 : (0 <= max)) (PreH8 : (size = 0)) (PreH9 : ((string_length (input)) < INT_MAX)) (PreH10 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH11 : (problem_111_pre_z input )) (PreH12 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH13 : (problem_111_scan_state_z input i counts_2 max )) (PreH14 : (valid_string input )) (PreH15 : (out <> 0)) (PreH16 : (keys <> 0)) (PreH17 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_entail_wit_5 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) = 0)) (PreH2 : (0 <= i)) (PreH3 : (i <= (string_length (input)))) (PreH4 : ((Zlength (counts_2)) = 256)) (PreH5 : (0 <= max)) (PreH6 : (size = 0)) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH9 : (problem_111_pre_z input )) (PreH10 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH11 : (problem_111_scan_state_z input i counts_2 max )) (PreH12 : (valid_string input )) (PreH13 : (out <> 0)) (PreH14 : (keys <> 0)) (PreH15 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (value_list: (@list Z))  (key_list: (@list Z))  (counts: (@list Z)) ,
  “ (i = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= 0) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max 0 key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts_2: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) = 0)) (PreH3 : (0 <= i)) (PreH4 : (i <= (string_length (input)))) (PreH5 : ((Zlength (counts_2)) = 256)) (PreH6 : (0 <= max)) (PreH7 : (size = 0)) (PreH8 : ((string_length (input)) < INT_MAX)) (PreH9 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts_2) (0))) /\ ((Znth (z) (counts_2) (0)) <= i)))) (PreH10 : (problem_111_pre_z input )) (PreH11 : forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (string_length (input)))) -> ((0 <= (Znth (k_2) (input) (0))) /\ ((Znth (k_2) (input) (0)) < 256)))) (PreH12 : (problem_111_scan_state_z input i counts_2 max )) (PreH13 : (valid_string input )) (PreH14 : (out <> 0)) (PreH15 : (keys <> 0)) (PreH16 : (values <> 0)) ,
  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  EX (value_list: (@list Z))  (key_list: (@list Z)) ,
  “ (i = (string_length (input))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= 0) ” 
  &&  “ ((Zlength (counts_2)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts_2 max ) ” 
  &&  “ (problem_111_output_prefix_z counts_2 max 0 key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (CharArray.undef_full keys 256 )
  **  (CharArray.seg keys 0 size key_list )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
).

Definition histogram_entail_wit_6_1 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.seg values 0 (size + 1 ) (app (value_list_2) ((cons ((Znth ch counts_2 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg values (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list_2) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
|--
  EX (value_list: (@list Z))  (key_list: (@list Z))  (counts: (@list Z)) ,
  “ (i = (string_length (input))) ” 
  &&  “ (0 <= (ch + 1 )) ” 
  &&  “ ((ch + 1 ) <= 256) ” 
  &&  “ (0 <= (size + 1 )) ” 
  &&  “ ((size + 1 ) <= (ch + 1 )) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = (size + 1 )) ” 
  &&  “ ((Zlength (value_list)) = (size + 1 )) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max (ch + 1 ) key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) key_list )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (IntArray.seg values 0 (size + 1 ) value_list )
  **  (IntArray.undef_seg values (size + 1 ) 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  TT && emp 
|--
  “ (problem_111_output_prefix_z counts_2 max (ch + 1 ) (app (key_list_2) ((cons (ch) ((@nil Z))))) (app (value_list_2) ((cons ((Znth ch counts_2 0)) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((app (value_list_2) ((cons ((Znth ch counts_2 0)) ((@nil Z))))))) = (size + 1 )) ” 
  &&  “ ((Zlength ((app (key_list_2) ((cons (ch) ((@nil Z))))))) = (size + 1 )) ”
  &&  emp
).

Definition histogram_entail_wit_6_1_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (problem_111_output_prefix_z counts_2 max (ch + 1 ) (app (key_list_2) ((cons (ch) ((@nil Z))))) (app (value_list_2) ((cons ((Znth ch counts_2 0)) ((@nil Z))))) )
.

Definition histogram_entail_wit_6_1_split_goal_2 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  ((Zlength ((app (value_list_2) ((cons ((Znth ch counts_2 0)) ((@nil Z))))))) = (size + 1 ))
.

Definition histogram_entail_wit_6_1_split_goal_3 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  ((Zlength ((app (key_list_2) ((cons (ch) ((@nil Z))))))) = (size + 1 ))
.

Definition histogram_entail_wit_6_2 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : ((Znth ch counts_2 0) <> max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (ch < 256)) (PreH4 : (i = (string_length (input)))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 256)) (PreH7 : (0 <= size)) (PreH8 : (size <= ch)) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : ((Zlength (key_list_2)) = size)) (PreH11 : ((Zlength (value_list_2)) = size)) (PreH12 : (problem_111_pre_z input )) (PreH13 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH14 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list_2 )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list_2 )
  **  (IntArray.undef_seg values size 256 )
|--
  EX (value_list: (@list Z))  (key_list: (@list Z))  (counts: (@list Z)) ,
  “ (i = (string_length (input))) ” 
  &&  “ (0 <= (ch + 1 )) ” 
  &&  “ ((ch + 1 ) <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= (ch + 1 )) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max (ch + 1 ) key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : ((Znth ch counts_2 0) <> max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (ch < 256)) (PreH4 : (i = (string_length (input)))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 256)) (PreH7 : (0 <= size)) (PreH8 : (size <= ch)) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : ((Zlength (key_list_2)) = size)) (PreH11 : ((Zlength (value_list_2)) = size)) (PreH12 : (problem_111_pre_z input )) (PreH13 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH14 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  TT && emp 
|--
  “ (problem_111_output_prefix_z counts_2 max (ch + 1 ) key_list_2 value_list_2 ) ”
  &&  emp
).

Definition histogram_entail_wit_6_2_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : ((Znth ch counts_2 0) <> max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (ch < 256)) (PreH4 : (i = (string_length (input)))) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 256)) (PreH7 : (0 <= size)) (PreH8 : (size <= ch)) (PreH9 : ((Zlength (counts_2)) = 256)) (PreH10 : ((Zlength (key_list_2)) = size)) (PreH11 : ((Zlength (value_list_2)) = size)) (PreH12 : (problem_111_pre_z input )) (PreH13 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH14 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  (problem_111_output_prefix_z counts_2 max (ch + 1 ) key_list_2 value_list_2 )
.

Definition histogram_entail_wit_6_3 := 
(
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts_2 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list_2 )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list_2 )
  **  (IntArray.undef_seg values size 256 )
|--
  EX (value_list: (@list Z))  (key_list: (@list Z))  (counts: (@list Z)) ,
  “ (i = (string_length (input))) ” 
  &&  “ (0 <= (ch + 1 )) ” 
  &&  “ ((ch + 1 ) <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= (ch + 1 )) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max (ch + 1 ) key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
) \/
(
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  TT && emp 
|--
  “ (problem_111_output_prefix_z counts_2 max (ch + 1 ) key_list_2 value_list_2 ) ”
  &&  emp
).

Definition histogram_entail_wit_6_3_split_goal_1 := 
forall (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts_2: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max <= 0)) (PreH2 : ((Znth ch counts_2 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts_2)) = 256)) (PreH11 : ((Zlength (key_list_2)) = size)) (PreH12 : ((Zlength (value_list_2)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts_2 max )) (PreH15 : (problem_111_output_prefix_z counts_2 max ch key_list_2 value_list_2 )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (problem_111_output_prefix_z counts_2 max (ch + 1 ) key_list_2 value_list_2 )
.

Definition histogram_return_wit_1 := 
forall (test_pre: Z) (input: (@list Z)) (values_2: Z) (keys_2: Z) (out: Z) (max: Z) (value_list_2: (@list Z)) (key_list_2: (@list Z)) (counts: (@list Z)) (size_2: Z) (ch: Z) (i: Z) (PreH1 : (ch >= 256)) (PreH2 : (i = (string_length (input)))) (PreH3 : (0 <= ch)) (PreH4 : (ch <= 256)) (PreH5 : (0 <= size_2)) (PreH6 : (size_2 <= ch)) (PreH7 : ((Zlength (counts)) = 256)) (PreH8 : ((Zlength (key_list_2)) = size_2)) (PreH9 : ((Zlength (value_list_2)) = size_2)) (PreH10 : (problem_111_pre_z input )) (PreH11 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH12 : (problem_111_output_prefix_z counts max ch key_list_2 value_list_2 )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (out <> 0)) (PreH15 : (keys_2 <> 0)) (PreH16 : (values_2 <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size_2)
  **  (store_string test_pre input )
  **  (CharArray.seg keys_2 0 size_2 key_list_2 )
  **  (CharArray.undef_seg keys_2 size_2 256 )
  **  (IntArray.seg values_2 0 size_2 value_list_2 )
  **  (IntArray.undef_seg values_2 size_2 256 )
|--
  (EX (size: Z)  (values: Z)  (keys: Z) ,
  “ (out <> 0) ” 
  &&  “ (keys = 0) ” 
  &&  “ (size = 0) ”
  &&  (store_string test_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size))
  ||
  (EX (size: Z)  (values: Z)  (keys: Z) ,
  “ (out <> 0) ” 
  &&  “ (values = 0) ” 
  &&  “ (size = 0) ”
  &&  (store_string test_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size))
  ||
  (EX (value_list: (@list Z))  (key_list: (@list Z))  (size: Z)  (values: Z)  (keys: Z) ,
  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_spec_z input key_list value_list ) ”
  &&  (store_string test_pre input )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> size)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 ))
.

Definition histogram_partial_solve_wit_1 := 
forall (test_pre: Z) (input: (@list Z)) (PreH1 : (valid_string input )) (PreH2 : ((string_length (input)) < INT_MAX)) (PreH3 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH4 : (problem_111_pre_z input )) ,
  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  (store_string test_pre input )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_pre_z input ) ”
  &&  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
.

Definition histogram_partial_solve_wit_2_pure := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : ((string_length (input)) < INT_MAX)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH6 : (problem_111_pre_z input )) ,
  ((( &( "keys" ) )) # Ptr  |->_)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ”
.

Definition histogram_partial_solve_wit_2_aux := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : (valid_string input )) (PreH4 : ((string_length (input)) < INT_MAX)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH6 : (problem_111_pre_z input )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_pre_z input ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
.

Definition histogram_partial_solve_wit_2 := histogram_partial_solve_wit_2_pure -> histogram_partial_solve_wit_2_aux.

Definition histogram_partial_solve_wit_3_pure := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH7 : (problem_111_pre_z input )) ,
  ((( &( "values" ) )) # Ptr  |->_)
  **  (CharArray.undef_full retval_2 256 )
  **  ((( &( "keys" ) )) # Ptr  |-> retval_2)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
  **  ((( &( "test" ) )) # Ptr  |-> test_pre)
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ”
.

Definition histogram_partial_solve_wit_3_aux := 
forall (test_pre: Z) (input: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (valid_string input )) (PreH5 : ((string_length (input)) < INT_MAX)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH7 : (problem_111_pre_z input )) ,
  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
|--
  “ (0 <= 256) ” 
  &&  “ (256 < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (valid_string input ) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_pre_z input ) ”
  &&  (CharArray.undef_full retval_2 256 )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_full ( &( "count" ) ) 256 )
.

Definition histogram_partial_solve_wit_3 := histogram_partial_solve_wit_3_pure -> histogram_partial_solve_wit_3_aux.

Definition histogram_partial_solve_wit_4 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (size: Z) (i: Z) (PreH1 : (i < 256)) (PreH2 : (0 <= i)) (PreH3 : (i <= 256)) (PreH4 : (size = 0)) (PreH5 : (max = 0)) (PreH6 : (0 <= (string_length (input)))) (PreH7 : ((string_length (input)) < INT_MAX)) (PreH8 : (problem_111_pre_z input )) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH10 : (valid_string input )) (PreH11 : (out <> 0)) (PreH12 : (keys <> 0)) (PreH13 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (IntArray.undef_seg ( &( "count" ) ) i 256 )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (i < 256) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 256) ” 
  &&  “ (size = 0) ” 
  &&  “ (max = 0) ” 
  &&  “ (0 <= (string_length (input))) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + (i * sizeof(INT)))) # Int  |->_)
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.undef_seg ( &( "count" ) ) (i + 1 ) 256 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg ( &( "count" ) ) 0 i (zeros (i)) )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_5 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth i (c_string (input)) 0) < 256)) (PreH2 : (0 <= (Znth i (c_string (input)) 0))) (PreH3 : ((Znth i (c_string (input)) 0) <> 32)) (PreH4 : ((Znth i (c_string (input)) 0) <> 0)) (PreH5 : (0 <= i)) (PreH6 : (i <= (string_length (input)))) (PreH7 : ((Zlength (counts)) = 256)) (PreH8 : (0 <= max)) (PreH9 : (size = 0)) (PreH10 : ((string_length (input)) < INT_MAX)) (PreH11 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH12 : (problem_111_pre_z input )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (problem_111_scan_state_z input i counts max )) (PreH15 : (valid_string input )) (PreH16 : (out <> 0)) (PreH17 : (keys <> 0)) (PreH18 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 256) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input i counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + ((Znth i (c_string (input)) 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i (c_string (input)) 0) counts 0))
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i (c_string (input)) 0) 0 256 counts )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_6 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 256) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input i counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + ((Znth i (c_string (input)) 0) * sizeof(INT)))) # Int  |->_)
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i (c_string (input)) 0) 0 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_7 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input)) + 1 ))) (PreH2 : ((Znth i (c_string (input)) 0) < 256)) (PreH3 : (0 <= (Znth i (c_string (input)) 0))) (PreH4 : ((Znth i (c_string (input)) 0) <> 32)) (PreH5 : ((Znth i (c_string (input)) 0) <> 0)) (PreH6 : (0 <= i)) (PreH7 : (i <= (string_length (input)))) (PreH8 : ((Zlength (counts)) = 256)) (PreH9 : (0 <= max)) (PreH10 : (size = 0)) (PreH11 : ((string_length (input)) < INT_MAX)) (PreH12 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH13 : (problem_111_pre_z input )) (PreH14 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH15 : (problem_111_scan_state_z input i counts max )) (PreH16 : (valid_string input )) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 256) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input i counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + ((Znth i (c_string (input)) 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0))
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i (c_string (input)) 0) 0 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_8 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (size: Z) (max: Z) (counts: (@list Z)) (i: Z) (PreH1 : ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0) > max)) (PreH2 : (0 <= ((string_length (input)) + 1 ))) (PreH3 : ((Znth i (c_string (input)) 0) < 256)) (PreH4 : (0 <= (Znth i (c_string (input)) 0))) (PreH5 : ((Znth i (c_string (input)) 0) <> 32)) (PreH6 : ((Znth i (c_string (input)) 0) <> 0)) (PreH7 : (0 <= i)) (PreH8 : (i <= (string_length (input)))) (PreH9 : ((Zlength (counts)) = 256)) (PreH10 : (0 <= max)) (PreH11 : (size = 0)) (PreH12 : ((string_length (input)) < INT_MAX)) (PreH13 : forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i)))) (PreH14 : (problem_111_pre_z input )) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH16 : (problem_111_scan_state_z input i counts max )) (PreH17 : (valid_string input )) (PreH18 : (out <> 0)) (PreH19 : (keys <> 0)) (PreH20 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
|--
  “ ((Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0) > max) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ ((Znth i (c_string (input)) 0) < 256) ” 
  &&  “ (0 <= (Znth i (c_string (input)) 0)) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 32) ” 
  &&  “ ((Znth i (c_string (input)) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (string_length (input))) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ (0 <= max) ” 
  &&  “ (size = 0) ” 
  &&  “ ((string_length (input)) < INT_MAX) ” 
  &&  “ forall (z: Z) , (((0 <= z) /\ (z < 256)) -> ((0 <= (Znth (z) (counts) (0))) /\ ((Znth (z) (counts) (0)) <= i))) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (problem_111_scan_state_z input i counts max ) ” 
  &&  “ (valid_string input ) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + ((Znth i (c_string (input)) 0) * sizeof(INT)))) # Int  |-> (Znth (Znth i (c_string (input)) 0) (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) 0))
  **  (IntArray.missing_i ( &( "count" ) ) (Znth i (c_string (input)) 0) 0 256 (replace_Znth ((Znth i (c_string (input)) 0)) (((Znth (Znth i (c_string (input)) 0) counts 0) + 1 )) (counts)) )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.undef_full keys 256 )
  **  (IntArray.undef_full values 256 )
.

Definition histogram_partial_solve_wit_9 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (ch < 256)) (PreH2 : (i = (string_length (input)))) (PreH3 : (0 <= ch)) (PreH4 : (ch <= 256)) (PreH5 : (0 <= size)) (PreH6 : (size <= ch)) (PreH7 : ((Zlength (counts)) = 256)) (PreH8 : ((Zlength (key_list)) = size)) (PreH9 : ((Zlength (value_list)) = size)) (PreH10 : (problem_111_pre_z input )) (PreH11 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH12 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH13 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH14 : (out <> 0)) (PreH15 : (keys <> 0)) (PreH16 : (values <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string test_pre input )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (ch < 256) ” 
  &&  “ (i = (string_length (input))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= ch) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max ch key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + (ch * sizeof(INT)))) # Int  |-> (Znth ch counts 0))
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  (IntArray.missing_i ( &( "count" ) ) ch 0 256 counts )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
.

Definition histogram_partial_solve_wit_10 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (CharArray.undef_seg keys size 256 )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (max > 0) ” 
  &&  “ ((Znth ch counts 0) = max) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (ch < 256) ” 
  &&  “ (i = (string_length (input))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= ch) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max ch key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((keys + (size * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i keys size size 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.seg keys 0 size key_list )
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
.

Definition histogram_partial_solve_wit_11 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (max > 0) ” 
  &&  “ ((Znth ch counts 0) = max) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (ch < 256) ” 
  &&  “ (i = (string_length (input))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= ch) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max ch key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((( &( "count" ) ) + (ch * sizeof(INT)))) # Int  |-> (Znth ch counts 0))
  **  (IntArray.missing_i ( &( "count" ) ) ch 0 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
.

Definition histogram_partial_solve_wit_12 := 
forall (test_pre: Z) (input: (@list Z)) (values: Z) (keys: Z) (out: Z) (max: Z) (value_list: (@list Z)) (key_list: (@list Z)) (counts: (@list Z)) (size: Z) (ch: Z) (i: Z) (PreH1 : (max > 0)) (PreH2 : ((Znth ch counts 0) = max)) (PreH3 : (0 <= ((string_length (input)) + 1 ))) (PreH4 : (ch < 256)) (PreH5 : (i = (string_length (input)))) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 256)) (PreH8 : (0 <= size)) (PreH9 : (size <= ch)) (PreH10 : ((Zlength (counts)) = 256)) (PreH11 : ((Zlength (key_list)) = size)) (PreH12 : ((Zlength (value_list)) = size)) (PreH13 : (problem_111_pre_z input )) (PreH14 : (problem_111_scan_state_z input (string_length (input)) counts max )) (PreH15 : (problem_111_output_prefix_z counts max ch key_list value_list )) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256)))) (PreH17 : (out <> 0)) (PreH18 : (keys <> 0)) (PreH19 : (values <> 0)) ,
  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg values 0 size value_list )
  **  (IntArray.undef_seg values size 256 )
|--
  “ (max > 0) ” 
  &&  “ ((Znth ch counts 0) = max) ” 
  &&  “ (0 <= ((string_length (input)) + 1 )) ” 
  &&  “ (ch < 256) ” 
  &&  “ (i = (string_length (input))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 256) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= ch) ” 
  &&  “ ((Zlength (counts)) = 256) ” 
  &&  “ ((Zlength (key_list)) = size) ” 
  &&  “ ((Zlength (value_list)) = size) ” 
  &&  “ (problem_111_pre_z input ) ” 
  &&  “ (problem_111_scan_state_z input (string_length (input)) counts max ) ” 
  &&  “ (problem_111_output_prefix_z counts max ch key_list value_list ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (string_length (input)))) -> ((0 <= (Znth (k) (input) (0))) /\ ((Znth (k) (input) (0)) < 256))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (keys <> 0) ” 
  &&  “ (values <> 0) ”
  &&  (((values + (size * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg values (size + 1 ) 256 )
  **  (IntArray.full ( &( "count" ) ) 256 counts )
  **  (CharArray.seg keys 0 (size + 1 ) (app (key_list) ((cons (ch) ((@nil Z))))) )
  **  (CharArray.undef_seg keys (size + 1 ) 256 )
  **  (CharArray.full test_pre ((string_length (input)) + 1 ) (c_string (input)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "keys")) # Ptr  |-> keys)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "values")) # Ptr  |-> values)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.seg values 0 size value_list )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_histogram_safety_wit_1 : histogram_safety_wit_1.
Axiom proof_of_histogram_safety_wit_2 : histogram_safety_wit_2.
Axiom proof_of_histogram_safety_wit_3 : histogram_safety_wit_3.
Axiom proof_of_histogram_safety_wit_4 : histogram_safety_wit_4.
Axiom proof_of_histogram_safety_wit_5 : histogram_safety_wit_5.
Axiom proof_of_histogram_safety_wit_6 : histogram_safety_wit_6.
Axiom proof_of_histogram_safety_wit_7 : histogram_safety_wit_7.
Axiom proof_of_histogram_safety_wit_8 : histogram_safety_wit_8.
Axiom proof_of_histogram_safety_wit_9 : histogram_safety_wit_9.
Axiom proof_of_histogram_safety_wit_10 : histogram_safety_wit_10.
Axiom proof_of_histogram_safety_wit_11 : histogram_safety_wit_11.
Axiom proof_of_histogram_safety_wit_12 : histogram_safety_wit_12.
Axiom proof_of_histogram_safety_wit_13 : histogram_safety_wit_13.
Axiom proof_of_histogram_safety_wit_14 : histogram_safety_wit_14.
Axiom proof_of_histogram_safety_wit_15 : histogram_safety_wit_15.
Axiom proof_of_histogram_safety_wit_16 : histogram_safety_wit_16.
Axiom proof_of_histogram_safety_wit_17 : histogram_safety_wit_17.
Axiom proof_of_histogram_safety_wit_18 : histogram_safety_wit_18.
Axiom proof_of_histogram_safety_wit_19 : histogram_safety_wit_19.
Axiom proof_of_histogram_safety_wit_20 : histogram_safety_wit_20.
Axiom proof_of_histogram_safety_wit_21 : histogram_safety_wit_21.
Axiom proof_of_histogram_safety_wit_22 : histogram_safety_wit_22.
Axiom proof_of_histogram_safety_wit_23 : histogram_safety_wit_23.
Axiom proof_of_histogram_safety_wit_24 : histogram_safety_wit_24.
Axiom proof_of_histogram_safety_wit_25 : histogram_safety_wit_25.
Axiom proof_of_histogram_safety_wit_26 : histogram_safety_wit_26.
Axiom proof_of_histogram_safety_wit_27 : histogram_safety_wit_27.
Axiom proof_of_histogram_safety_wit_28 : histogram_safety_wit_28.
Axiom proof_of_histogram_safety_wit_29 : histogram_safety_wit_29.
Axiom proof_of_histogram_entail_wit_1 : histogram_entail_wit_1.
Axiom proof_of_histogram_entail_wit_2 : histogram_entail_wit_2.
Axiom proof_of_histogram_entail_wit_3 : histogram_entail_wit_3.
Axiom proof_of_histogram_entail_wit_4_1 : histogram_entail_wit_4_1.
Axiom proof_of_histogram_entail_wit_4_2 : histogram_entail_wit_4_2.
Axiom proof_of_histogram_entail_wit_4_3 : histogram_entail_wit_4_3.
Axiom proof_of_histogram_entail_wit_4_4 : histogram_entail_wit_4_4.
Axiom proof_of_histogram_entail_wit_4_5 : histogram_entail_wit_4_5.
Axiom proof_of_histogram_entail_wit_5 : histogram_entail_wit_5.
Axiom proof_of_histogram_entail_wit_6_1 : histogram_entail_wit_6_1.
Axiom proof_of_histogram_entail_wit_6_2 : histogram_entail_wit_6_2.
Axiom proof_of_histogram_entail_wit_6_3 : histogram_entail_wit_6_3.
Axiom proof_of_histogram_return_wit_1 : histogram_return_wit_1.
Axiom proof_of_histogram_partial_solve_wit_1 : histogram_partial_solve_wit_1.
Axiom proof_of_histogram_partial_solve_wit_2_pure : histogram_partial_solve_wit_2_pure.
Axiom proof_of_histogram_partial_solve_wit_2 : histogram_partial_solve_wit_2.
Axiom proof_of_histogram_partial_solve_wit_3_pure : histogram_partial_solve_wit_3_pure.
Axiom proof_of_histogram_partial_solve_wit_3 : histogram_partial_solve_wit_3.
Axiom proof_of_histogram_partial_solve_wit_4 : histogram_partial_solve_wit_4.
Axiom proof_of_histogram_partial_solve_wit_5 : histogram_partial_solve_wit_5.
Axiom proof_of_histogram_partial_solve_wit_6 : histogram_partial_solve_wit_6.
Axiom proof_of_histogram_partial_solve_wit_7 : histogram_partial_solve_wit_7.
Axiom proof_of_histogram_partial_solve_wit_8 : histogram_partial_solve_wit_8.
Axiom proof_of_histogram_partial_solve_wit_9 : histogram_partial_solve_wit_9.
Axiom proof_of_histogram_partial_solve_wit_10 : histogram_partial_solve_wit_10.
Axiom proof_of_histogram_partial_solve_wit_11 : histogram_partial_solve_wit_11.
Axiom proof_of_histogram_partial_solve_wit_12 : histogram_partial_solve_wit_12.

End VC_Correct.
