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
Require Import p105_by_length.
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

(*----- Function by_length -----*)

Definition by_length_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  ((( &( "five" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |-> ((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Six"%string))) ("Six"%string) )
  **  ((( &( "six" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  ((( &( "five" ) )) # Ptr  |-> ((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |-> ((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Seven"%string))) ("Seven"%string) )
  **  ((( &( "seven" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Six"%string))) ("Six"%string) )
  **  ((( &( "six" ) )) # Ptr  |-> ((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  ((( &( "five" ) )) # Ptr  |-> ((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |-> ((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Eight"%string))) ("Eight"%string) )
  **  ((( &( "eight" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Seven"%string))) ("Seven"%string) )
  **  ((( &( "seven" ) )) # Ptr  |-> ((LitMap (("Seven"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Six"%string))) ("Six"%string) )
  **  ((( &( "six" ) )) # Ptr  |-> ((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  ((( &( "five" ) )) # Ptr  |-> ((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |-> ((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Nine"%string))) ("Nine"%string) )
  **  ((( &( "nine" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("Eight"%string))) ("Eight"%string) )
  **  ((( &( "eight" ) )) # Ptr  |-> ((LitMap (("Eight"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Seven"%string))) ("Seven"%string) )
  **  ((( &( "seven" ) )) # Ptr  |-> ((LitMap (("Seven"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Six"%string))) ("Six"%string) )
  **  ((( &( "six" ) )) # Ptr  |-> ((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  ((( &( "five" ) )) # Ptr  |-> ((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  ((( &( "four" ) )) # Ptr  |-> ((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  ((( &( "three" ) )) # Ptr  |-> ((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  ((( &( "two" ) )) # Ptr  |-> ((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ))
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  ((( &( "one" ) )) # Ptr  |-> ((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (arr_pre <> 0)) (PreH12 : (0 <= arr_size_pre)) (PreH13 : (arr_size_pre < INT_MAX)) (PreH14 : (arr_size_pre = (Zlength (input_l)))) (PreH15 : (problem_105_pre_z input_l )) (PreH16 : (digit_payloads_string_safe_105 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  (IntArray.undef_full retval_3 arr_size_pre )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  (IntArray.undef_full retval_3 arr_size_pre )
  **  ((( &( "tmp" ) )) # Ptr  |-> retval_3)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  (IntArray.seg tmp 0 (i + 1 ) (app (tmp_l) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition by_length_safety_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (digit_payloads_string_safe_105 )) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition by_length_safety_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) ,
  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_16 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition by_length_safety_wit_17 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (k: Z) (i: Z) (d: Z) (sorted_l: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH27 : (out_size = (Zlength (output_rows)))) (PreH28 : (out_size = (Zlength (output_ptrs)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (((arr_size_pre - 1 ) - k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size_pre - 1 ) - k )) ”
.

Definition by_length_safety_wit_18 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (k: Z) (i: Z) (d: Z) (sorted_l: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH27 : (out_size = (Zlength (output_rows)))) (PreH28 : (out_size = (Zlength (output_ptrs)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((arr_size_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size_pre - 1 )) ”
.

Definition by_length_safety_wit_19 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (k: Z) (i: Z) (d: Z) (sorted_l: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH27 : (out_size = (Zlength (output_rows)))) (PreH28 : (out_size = (Zlength (output_ptrs)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition by_length_safety_wit_20 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l )) (PreH20 : (Permutation input_l sorted_l )) (PreH21 : (int_range_list_105 sorted_l )) (PreH22 : (digit_payloads_string_safe_105 )) (PreH23 : (0 <= k)) (PreH24 : (k < arr_size_pre)) (PreH25 : (0 <= i)) (PreH26 : (i < arr_size_pre)) (PreH27 : (i = ((arr_size_pre - 1 ) - k ))) (PreH28 : (INT_MIN <= d)) (PreH29 : (d <= INT_MAX)) (PreH30 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH31 : (out_size = (Zlength (output_rows)))) (PreH32 : (out_size = (Zlength (output_ptrs)))) (PreH33 : (0 <= out_size)) (PreH34 : (out_size <= k)) (PreH35 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH36 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition by_length_safety_wit_21 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d >= 1)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l )) (PreH21 : (Permutation input_l sorted_l )) (PreH22 : (int_range_list_105 sorted_l )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k < arr_size_pre)) (PreH26 : (0 <= i)) (PreH27 : (i < arr_size_pre)) (PreH28 : (i = ((arr_size_pre - 1 ) - k ))) (PreH29 : (INT_MIN <= d)) (PreH30 : (d <= INT_MAX)) (PreH31 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH32 : (out_size = (Zlength (output_rows)))) (PreH33 : (out_size = (Zlength (output_ptrs)))) (PreH34 : (0 <= out_size)) (PreH35 : (out_size <= k)) (PreH36 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH37 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (9 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 9) ”
.

Definition by_length_safety_wit_22 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <= 9)) (PreH2 : (d >= 1)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (arr_size_pre = (Zlength (sorted_l)))) (PreH20 : (problem_105_pre_z input_l )) (PreH21 : (sorted_int_list_by 1 sorted_l )) (PreH22 : (Permutation input_l sorted_l )) (PreH23 : (int_range_list_105 sorted_l )) (PreH24 : (digit_payloads_string_safe_105 )) (PreH25 : (0 <= k)) (PreH26 : (k < arr_size_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < arr_size_pre)) (PreH29 : (i = ((arr_size_pre - 1 ) - k ))) (PreH30 : (INT_MIN <= d)) (PreH31 : (d <= INT_MAX)) (PreH32 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH33 : (out_size = (Zlength (output_rows)))) (PreH34 : (out_size = (Zlength (output_ptrs)))) (PreH35 : (0 <= out_size)) (PreH36 : (out_size <= k)) (PreH37 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH38 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition by_length_safety_wit_23 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 1)) (PreH2 : (d <= 9)) (PreH3 : (d >= 1)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (tmp <> 0)) (PreH16 : (arr_pre <> 0)) (PreH17 : (0 <= arr_size_pre)) (PreH18 : (arr_size_pre < INT_MAX)) (PreH19 : (arr_size_pre = (Zlength (input_l)))) (PreH20 : (arr_size_pre = (Zlength (sorted_l)))) (PreH21 : (problem_105_pre_z input_l )) (PreH22 : (sorted_int_list_by 1 sorted_l )) (PreH23 : (Permutation input_l sorted_l )) (PreH24 : (int_range_list_105 sorted_l )) (PreH25 : (digit_payloads_string_safe_105 )) (PreH26 : (0 <= k)) (PreH27 : (k < arr_size_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < arr_size_pre)) (PreH30 : (i = ((arr_size_pre - 1 ) - k ))) (PreH31 : (INT_MIN <= d)) (PreH32 : (d <= INT_MAX)) (PreH33 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH34 : (out_size = (Zlength (output_rows)))) (PreH35 : (out_size = (Zlength (output_ptrs)))) (PreH36 : (0 <= out_size)) (PreH37 : (out_size <= k)) (PreH38 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH39 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition by_length_safety_wit_24 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 2)) (PreH2 : (d <> 1)) (PreH3 : (d <= 9)) (PreH4 : (d >= 1)) (PreH5 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH6 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH7 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH8 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH9 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH10 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH11 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH12 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH13 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (tmp <> 0)) (PreH17 : (arr_pre <> 0)) (PreH18 : (0 <= arr_size_pre)) (PreH19 : (arr_size_pre < INT_MAX)) (PreH20 : (arr_size_pre = (Zlength (input_l)))) (PreH21 : (arr_size_pre = (Zlength (sorted_l)))) (PreH22 : (problem_105_pre_z input_l )) (PreH23 : (sorted_int_list_by 1 sorted_l )) (PreH24 : (Permutation input_l sorted_l )) (PreH25 : (int_range_list_105 sorted_l )) (PreH26 : (digit_payloads_string_safe_105 )) (PreH27 : (0 <= k)) (PreH28 : (k < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= d)) (PreH33 : (d <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH35 : (out_size = (Zlength (output_rows)))) (PreH36 : (out_size = (Zlength (output_ptrs)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH40 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition by_length_safety_wit_25 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 3)) (PreH2 : (d <> 2)) (PreH3 : (d <> 1)) (PreH4 : (d <= 9)) (PreH5 : (d >= 1)) (PreH6 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH7 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH8 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH9 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH10 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH11 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH12 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH13 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH14 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (tmp <> 0)) (PreH18 : (arr_pre <> 0)) (PreH19 : (0 <= arr_size_pre)) (PreH20 : (arr_size_pre < INT_MAX)) (PreH21 : (arr_size_pre = (Zlength (input_l)))) (PreH22 : (arr_size_pre = (Zlength (sorted_l)))) (PreH23 : (problem_105_pre_z input_l )) (PreH24 : (sorted_int_list_by 1 sorted_l )) (PreH25 : (Permutation input_l sorted_l )) (PreH26 : (int_range_list_105 sorted_l )) (PreH27 : (digit_payloads_string_safe_105 )) (PreH28 : (0 <= k)) (PreH29 : (k < arr_size_pre)) (PreH30 : (0 <= i)) (PreH31 : (i < arr_size_pre)) (PreH32 : (i = ((arr_size_pre - 1 ) - k ))) (PreH33 : (INT_MIN <= d)) (PreH34 : (d <= INT_MAX)) (PreH35 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH36 : (out_size = (Zlength (output_rows)))) (PreH37 : (out_size = (Zlength (output_ptrs)))) (PreH38 : (0 <= out_size)) (PreH39 : (out_size <= k)) (PreH40 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH41 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition by_length_safety_wit_26 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 4)) (PreH2 : (d <> 3)) (PreH3 : (d <> 2)) (PreH4 : (d <> 1)) (PreH5 : (d <= 9)) (PreH6 : (d >= 1)) (PreH7 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH8 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH9 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH10 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH11 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH12 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH13 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH14 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH15 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (tmp <> 0)) (PreH19 : (arr_pre <> 0)) (PreH20 : (0 <= arr_size_pre)) (PreH21 : (arr_size_pre < INT_MAX)) (PreH22 : (arr_size_pre = (Zlength (input_l)))) (PreH23 : (arr_size_pre = (Zlength (sorted_l)))) (PreH24 : (problem_105_pre_z input_l )) (PreH25 : (sorted_int_list_by 1 sorted_l )) (PreH26 : (Permutation input_l sorted_l )) (PreH27 : (int_range_list_105 sorted_l )) (PreH28 : (digit_payloads_string_safe_105 )) (PreH29 : (0 <= k)) (PreH30 : (k < arr_size_pre)) (PreH31 : (0 <= i)) (PreH32 : (i < arr_size_pre)) (PreH33 : (i = ((arr_size_pre - 1 ) - k ))) (PreH34 : (INT_MIN <= d)) (PreH35 : (d <= INT_MAX)) (PreH36 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH37 : (out_size = (Zlength (output_rows)))) (PreH38 : (out_size = (Zlength (output_ptrs)))) (PreH39 : (0 <= out_size)) (PreH40 : (out_size <= k)) (PreH41 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH42 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition by_length_safety_wit_27 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 5)) (PreH2 : (d <> 4)) (PreH3 : (d <> 3)) (PreH4 : (d <> 2)) (PreH5 : (d <> 1)) (PreH6 : (d <= 9)) (PreH7 : (d >= 1)) (PreH8 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH9 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH10 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH11 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH12 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH13 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH14 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH15 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH16 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (tmp <> 0)) (PreH20 : (arr_pre <> 0)) (PreH21 : (0 <= arr_size_pre)) (PreH22 : (arr_size_pre < INT_MAX)) (PreH23 : (arr_size_pre = (Zlength (input_l)))) (PreH24 : (arr_size_pre = (Zlength (sorted_l)))) (PreH25 : (problem_105_pre_z input_l )) (PreH26 : (sorted_int_list_by 1 sorted_l )) (PreH27 : (Permutation input_l sorted_l )) (PreH28 : (int_range_list_105 sorted_l )) (PreH29 : (digit_payloads_string_safe_105 )) (PreH30 : (0 <= k)) (PreH31 : (k < arr_size_pre)) (PreH32 : (0 <= i)) (PreH33 : (i < arr_size_pre)) (PreH34 : (i = ((arr_size_pre - 1 ) - k ))) (PreH35 : (INT_MIN <= d)) (PreH36 : (d <= INT_MAX)) (PreH37 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH38 : (out_size = (Zlength (output_rows)))) (PreH39 : (out_size = (Zlength (output_ptrs)))) (PreH40 : (0 <= out_size)) (PreH41 : (out_size <= k)) (PreH42 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH43 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (6 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 6) ”
.

Definition by_length_safety_wit_28 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 6)) (PreH2 : (d <> 5)) (PreH3 : (d <> 4)) (PreH4 : (d <> 3)) (PreH5 : (d <> 2)) (PreH6 : (d <> 1)) (PreH7 : (d <= 9)) (PreH8 : (d >= 1)) (PreH9 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH10 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH11 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH12 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH13 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH14 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH15 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH16 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH17 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (tmp <> 0)) (PreH21 : (arr_pre <> 0)) (PreH22 : (0 <= arr_size_pre)) (PreH23 : (arr_size_pre < INT_MAX)) (PreH24 : (arr_size_pre = (Zlength (input_l)))) (PreH25 : (arr_size_pre = (Zlength (sorted_l)))) (PreH26 : (problem_105_pre_z input_l )) (PreH27 : (sorted_int_list_by 1 sorted_l )) (PreH28 : (Permutation input_l sorted_l )) (PreH29 : (int_range_list_105 sorted_l )) (PreH30 : (digit_payloads_string_safe_105 )) (PreH31 : (0 <= k)) (PreH32 : (k < arr_size_pre)) (PreH33 : (0 <= i)) (PreH34 : (i < arr_size_pre)) (PreH35 : (i = ((arr_size_pre - 1 ) - k ))) (PreH36 : (INT_MIN <= d)) (PreH37 : (d <= INT_MAX)) (PreH38 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH39 : (out_size = (Zlength (output_rows)))) (PreH40 : (out_size = (Zlength (output_ptrs)))) (PreH41 : (0 <= out_size)) (PreH42 : (out_size <= k)) (PreH43 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH44 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (7 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 7) ”
.

Definition by_length_safety_wit_29 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 7)) (PreH2 : (d <> 6)) (PreH3 : (d <> 5)) (PreH4 : (d <> 4)) (PreH5 : (d <> 3)) (PreH6 : (d <> 2)) (PreH7 : (d <> 1)) (PreH8 : (d <= 9)) (PreH9 : (d >= 1)) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (arr_pre <> 0)) (PreH23 : (0 <= arr_size_pre)) (PreH24 : (arr_size_pre < INT_MAX)) (PreH25 : (arr_size_pre = (Zlength (input_l)))) (PreH26 : (arr_size_pre = (Zlength (sorted_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (sorted_int_list_by 1 sorted_l )) (PreH29 : (Permutation input_l sorted_l )) (PreH30 : (int_range_list_105 sorted_l )) (PreH31 : (digit_payloads_string_safe_105 )) (PreH32 : (0 <= k)) (PreH33 : (k < arr_size_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < arr_size_pre)) (PreH36 : (i = ((arr_size_pre - 1 ) - k ))) (PreH37 : (INT_MIN <= d)) (PreH38 : (d <= INT_MAX)) (PreH39 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH40 : (out_size = (Zlength (output_rows)))) (PreH41 : (out_size = (Zlength (output_ptrs)))) (PreH42 : (0 <= out_size)) (PreH43 : (out_size <= k)) (PreH44 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH45 : (d = (Znth (i) (sorted_l) (0)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition by_length_safety_wit_30 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 1)) (PreH2 : (d <= 9)) (PreH3 : (d >= 1)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (tmp <> 0)) (PreH16 : (arr_pre <> 0)) (PreH17 : (0 <= arr_size_pre)) (PreH18 : (arr_size_pre < INT_MAX)) (PreH19 : (arr_size_pre = (Zlength (input_l)))) (PreH20 : (arr_size_pre = (Zlength (sorted_l)))) (PreH21 : (problem_105_pre_z input_l )) (PreH22 : (sorted_int_list_by 1 sorted_l )) (PreH23 : (Permutation input_l sorted_l )) (PreH24 : (int_range_list_105 sorted_l )) (PreH25 : (digit_payloads_string_safe_105 )) (PreH26 : (0 <= k)) (PreH27 : (k < arr_size_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < arr_size_pre)) (PreH30 : (i = ((arr_size_pre - 1 ) - k ))) (PreH31 : (INT_MIN <= d)) (PreH32 : (d <= INT_MAX)) (PreH33 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH34 : (out_size = (Zlength (output_rows)))) (PreH35 : (out_size = (Zlength (output_ptrs)))) (PreH36 : (0 <= out_size)) (PreH37 : (out_size <= k)) (PreH38 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH39 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (one) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_31 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 2)) (PreH2 : (d <> 1)) (PreH3 : (d <= 9)) (PreH4 : (d >= 1)) (PreH5 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH6 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH7 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH8 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH9 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH10 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH11 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH12 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH13 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (tmp <> 0)) (PreH17 : (arr_pre <> 0)) (PreH18 : (0 <= arr_size_pre)) (PreH19 : (arr_size_pre < INT_MAX)) (PreH20 : (arr_size_pre = (Zlength (input_l)))) (PreH21 : (arr_size_pre = (Zlength (sorted_l)))) (PreH22 : (problem_105_pre_z input_l )) (PreH23 : (sorted_int_list_by 1 sorted_l )) (PreH24 : (Permutation input_l sorted_l )) (PreH25 : (int_range_list_105 sorted_l )) (PreH26 : (digit_payloads_string_safe_105 )) (PreH27 : (0 <= k)) (PreH28 : (k < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= d)) (PreH33 : (d <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH35 : (out_size = (Zlength (output_rows)))) (PreH36 : (out_size = (Zlength (output_ptrs)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH40 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (two) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_32 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 3)) (PreH2 : (d <> 2)) (PreH3 : (d <> 1)) (PreH4 : (d <= 9)) (PreH5 : (d >= 1)) (PreH6 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH7 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH8 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH9 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH10 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH11 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH12 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH13 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH14 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (tmp <> 0)) (PreH18 : (arr_pre <> 0)) (PreH19 : (0 <= arr_size_pre)) (PreH20 : (arr_size_pre < INT_MAX)) (PreH21 : (arr_size_pre = (Zlength (input_l)))) (PreH22 : (arr_size_pre = (Zlength (sorted_l)))) (PreH23 : (problem_105_pre_z input_l )) (PreH24 : (sorted_int_list_by 1 sorted_l )) (PreH25 : (Permutation input_l sorted_l )) (PreH26 : (int_range_list_105 sorted_l )) (PreH27 : (digit_payloads_string_safe_105 )) (PreH28 : (0 <= k)) (PreH29 : (k < arr_size_pre)) (PreH30 : (0 <= i)) (PreH31 : (i < arr_size_pre)) (PreH32 : (i = ((arr_size_pre - 1 ) - k ))) (PreH33 : (INT_MIN <= d)) (PreH34 : (d <= INT_MAX)) (PreH35 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH36 : (out_size = (Zlength (output_rows)))) (PreH37 : (out_size = (Zlength (output_ptrs)))) (PreH38 : (0 <= out_size)) (PreH39 : (out_size <= k)) (PreH40 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH41 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (three) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_33 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 4)) (PreH2 : (d <> 3)) (PreH3 : (d <> 2)) (PreH4 : (d <> 1)) (PreH5 : (d <= 9)) (PreH6 : (d >= 1)) (PreH7 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH8 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH9 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH10 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH11 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH12 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH13 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH14 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH15 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (tmp <> 0)) (PreH19 : (arr_pre <> 0)) (PreH20 : (0 <= arr_size_pre)) (PreH21 : (arr_size_pre < INT_MAX)) (PreH22 : (arr_size_pre = (Zlength (input_l)))) (PreH23 : (arr_size_pre = (Zlength (sorted_l)))) (PreH24 : (problem_105_pre_z input_l )) (PreH25 : (sorted_int_list_by 1 sorted_l )) (PreH26 : (Permutation input_l sorted_l )) (PreH27 : (int_range_list_105 sorted_l )) (PreH28 : (digit_payloads_string_safe_105 )) (PreH29 : (0 <= k)) (PreH30 : (k < arr_size_pre)) (PreH31 : (0 <= i)) (PreH32 : (i < arr_size_pre)) (PreH33 : (i = ((arr_size_pre - 1 ) - k ))) (PreH34 : (INT_MIN <= d)) (PreH35 : (d <= INT_MAX)) (PreH36 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH37 : (out_size = (Zlength (output_rows)))) (PreH38 : (out_size = (Zlength (output_ptrs)))) (PreH39 : (0 <= out_size)) (PreH40 : (out_size <= k)) (PreH41 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH42 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (four) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_34 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 5)) (PreH2 : (d <> 4)) (PreH3 : (d <> 3)) (PreH4 : (d <> 2)) (PreH5 : (d <> 1)) (PreH6 : (d <= 9)) (PreH7 : (d >= 1)) (PreH8 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH9 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH10 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH11 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH12 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH13 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH14 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH15 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH16 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (tmp <> 0)) (PreH20 : (arr_pre <> 0)) (PreH21 : (0 <= arr_size_pre)) (PreH22 : (arr_size_pre < INT_MAX)) (PreH23 : (arr_size_pre = (Zlength (input_l)))) (PreH24 : (arr_size_pre = (Zlength (sorted_l)))) (PreH25 : (problem_105_pre_z input_l )) (PreH26 : (sorted_int_list_by 1 sorted_l )) (PreH27 : (Permutation input_l sorted_l )) (PreH28 : (int_range_list_105 sorted_l )) (PreH29 : (digit_payloads_string_safe_105 )) (PreH30 : (0 <= k)) (PreH31 : (k < arr_size_pre)) (PreH32 : (0 <= i)) (PreH33 : (i < arr_size_pre)) (PreH34 : (i = ((arr_size_pre - 1 ) - k ))) (PreH35 : (INT_MIN <= d)) (PreH36 : (d <= INT_MAX)) (PreH37 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH38 : (out_size = (Zlength (output_rows)))) (PreH39 : (out_size = (Zlength (output_ptrs)))) (PreH40 : (0 <= out_size)) (PreH41 : (out_size <= k)) (PreH42 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH43 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (five) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_35 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 6)) (PreH2 : (d <> 5)) (PreH3 : (d <> 4)) (PreH4 : (d <> 3)) (PreH5 : (d <> 2)) (PreH6 : (d <> 1)) (PreH7 : (d <= 9)) (PreH8 : (d >= 1)) (PreH9 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH10 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH11 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH12 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH13 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH14 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH15 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH16 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH17 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (tmp <> 0)) (PreH21 : (arr_pre <> 0)) (PreH22 : (0 <= arr_size_pre)) (PreH23 : (arr_size_pre < INT_MAX)) (PreH24 : (arr_size_pre = (Zlength (input_l)))) (PreH25 : (arr_size_pre = (Zlength (sorted_l)))) (PreH26 : (problem_105_pre_z input_l )) (PreH27 : (sorted_int_list_by 1 sorted_l )) (PreH28 : (Permutation input_l sorted_l )) (PreH29 : (int_range_list_105 sorted_l )) (PreH30 : (digit_payloads_string_safe_105 )) (PreH31 : (0 <= k)) (PreH32 : (k < arr_size_pre)) (PreH33 : (0 <= i)) (PreH34 : (i < arr_size_pre)) (PreH35 : (i = ((arr_size_pre - 1 ) - k ))) (PreH36 : (INT_MIN <= d)) (PreH37 : (d <= INT_MAX)) (PreH38 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH39 : (out_size = (Zlength (output_rows)))) (PreH40 : (out_size = (Zlength (output_ptrs)))) (PreH41 : (0 <= out_size)) (PreH42 : (out_size <= k)) (PreH43 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH44 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (six) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_36 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 7)) (PreH2 : (d <> 6)) (PreH3 : (d <> 5)) (PreH4 : (d <> 4)) (PreH5 : (d <> 3)) (PreH6 : (d <> 2)) (PreH7 : (d <> 1)) (PreH8 : (d <= 9)) (PreH9 : (d >= 1)) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (arr_pre <> 0)) (PreH23 : (0 <= arr_size_pre)) (PreH24 : (arr_size_pre < INT_MAX)) (PreH25 : (arr_size_pre = (Zlength (input_l)))) (PreH26 : (arr_size_pre = (Zlength (sorted_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (sorted_int_list_by 1 sorted_l )) (PreH29 : (Permutation input_l sorted_l )) (PreH30 : (int_range_list_105 sorted_l )) (PreH31 : (digit_payloads_string_safe_105 )) (PreH32 : (0 <= k)) (PreH33 : (k < arr_size_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < arr_size_pre)) (PreH36 : (i = ((arr_size_pre - 1 ) - k ))) (PreH37 : (INT_MIN <= d)) (PreH38 : (d <= INT_MAX)) (PreH39 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH40 : (out_size = (Zlength (output_rows)))) (PreH41 : (out_size = (Zlength (output_ptrs)))) (PreH42 : (0 <= out_size)) (PreH43 : (out_size <= k)) (PreH44 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH45 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (seven) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_37 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l )) (PreH30 : (Permutation input_l sorted_l )) (PreH31 : (int_range_list_105 sorted_l )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH41 : (out_size = (Zlength (output_rows)))) (PreH42 : (out_size = (Zlength (output_ptrs)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (eight) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_38 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l )) (PreH30 : (Permutation input_l sorted_l )) (PreH31 : (int_range_list_105 sorted_l )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH41 : (out_size = (Zlength (output_rows)))) (PreH42 : (out_size = (Zlength (output_ptrs)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs)) + 1 ) (app (output_ptrs) ((cons (nine) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition by_length_safety_wit_39 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l )) (PreH20 : (Permutation input_l sorted_l )) (PreH21 : (int_range_list_105 sorted_l )) (PreH22 : (digit_payloads_string_safe_105 )) (PreH23 : (0 <= k)) (PreH24 : (k < arr_size_pre)) (PreH25 : (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs )) (PreH26 : (out_size = (Zlength (output_rows)))) (PreH27 : (out_size = (Zlength (output_ptrs)))) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= (k + 1 ))) (PreH30 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition by_length_entail_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (store_stringLit (LitMap (("Nine"%string))) ("Nine"%string) )
  **  (store_stringLit (LitMap (("Eight"%string))) ("Eight"%string) )
  **  (store_stringLit (LitMap (("Seven"%string))) ("Seven"%string) )
  **  (store_stringLit (LitMap (("Six"%string))) ("Six"%string) )
  **  (store_stringLit (LitMap (("Five"%string))) ("Five"%string) )
  **  (store_stringLit (LitMap (("Four"%string))) ("Four"%string) )
  **  (store_stringLit (LitMap (("Three"%string))) ("Three"%string) )
  **  (store_stringLit (LitMap (("Two"%string))) ("Two"%string) )
  **  (store_stringLit (LitMap (("One"%string))) ("One"%string) )
  **  (GlobalStrings_missing LitMap (cons (("One"%string)) ((@nil string))) )
  **  (IntArray.full arr_pre arr_size_pre input_l )
|--
  “ (((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (((LitMap (("Seven"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (((LitMap (("Eight"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (((LitMap (("Nine"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (((LitMap (("Nine"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (((LitMap (("Eight"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (((LitMap (("Seven"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (1))) ”
  &&  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_1_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (digit_payloads_string_safe_105 ) ”
.

Definition by_length_entail_wit_1_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Nine"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (9))) ”
.

Definition by_length_entail_wit_1_split_goal_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Eight"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (8))) ”
.

Definition by_length_entail_wit_1_split_goal_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Seven"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (7))) ”
.

Definition by_length_entail_wit_1_split_goal_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Six"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (6))) ”
.

Definition by_length_entail_wit_1_split_goal_6 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Five"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (5))) ”
.

Definition by_length_entail_wit_1_split_goal_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Four"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (4))) ”
.

Definition by_length_entail_wit_1_split_goal_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Three"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (3))) ”
.

Definition by_length_entail_wit_1_split_goal_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("Two"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (2))) ”
.

Definition by_length_entail_wit_1_split_goal_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  “ (((LitMap (("One"%string))) + (0 * sizeof(CHAR) ) ) = (digit_ptr_105 (LitMap) (1))) ”
.

Definition by_length_entail_wit_1_split_goal_spatial := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (PreH1 : (arr_pre <> 0)) (PreH2 : (0 <= arr_size_pre)) (PreH3 : (arr_size_pre < INT_MAX)) (PreH4 : (arr_size_pre = (Zlength (input_l)))) (PreH5 : (problem_105_pre_z input_l )) ,
  (GlobalStrings LitMap )
|--
  (digit_literals_heap_105 LitMap )
.

Definition by_length_entail_wit_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  (IntArray.undef_full retval_3 arr_size_pre )
  **  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (tmp_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (0 = (Zlength (tmp_l))) ” 
  &&  “ (tmp_l = (copy_prefix_105 (input_l) (0))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (IntArray.seg retval_3 0 0 tmp_l )
  **  (IntArray.undef_seg retval_3 0 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((@nil Z) = (copy_prefix_105 (input_l) (0))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ”
  &&  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_2_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((@nil Z) = (copy_prefix_105 (input_l) (0))) ”
.

Definition by_length_entail_wit_2_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition by_length_entail_wit_2_split_goal_spatial := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_entail_wit_3 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l_2)))) (PreH24 : (tmp_l_2 = (copy_prefix_105 (input_l) (i)))) ,
  (IntArray.seg tmp 0 (i + 1 ) (app (tmp_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) )
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (tmp_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= arr_size_pre) ” 
  &&  “ ((i + 1 ) = (Zlength (tmp_l))) ” 
  &&  “ (tmp_l = (copy_prefix_105 (input_l) ((i + 1 )))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 (i + 1 ) tmp_l )
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l_2)))) (PreH24 : (tmp_l_2 = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((i + 1 ) = (Zlength ((copy_prefix_105 (input_l) ((i + 1 )))))) ” 
  &&  “ ((app (tmp_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) = (copy_prefix_105 (input_l) ((i + 1 )))) ”
  &&  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_3_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l_2)))) (PreH24 : (tmp_l_2 = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((i + 1 ) = (Zlength ((copy_prefix_105 (input_l) ((i + 1 )))))) ”
.

Definition by_length_entail_wit_3_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l_2)))) (PreH24 : (tmp_l_2 = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ ((app (tmp_l_2) ((cons ((Znth i input_l 0)) ((@nil Z))))) = (copy_prefix_105 (input_l) ((i + 1 )))) ”
.

Definition by_length_entail_wit_3_split_goal_spatial := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l_2: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l_2)))) (PreH24 : (tmp_l_2 = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_entail_wit_4 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (digit_literals_heap_105 LitMap )
|--
  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_4_split_goal_spatial := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i >= arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (digit_literals_heap_105 LitMap )
|--
  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_entail_wit_5 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (IntArray.full tmp arr_size_pre sorted_full_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (int_range_list_105 sorted_full_l ) ” 
  &&  “ (Permutation input_l sorted_full_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_full_l ) ”
  &&  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_5_split_goal_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (int_range_list_105 sorted_full_l ) ”
.

Definition by_length_entail_wit_5_split_goal_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (Permutation input_l sorted_full_l ) ”
.

Definition by_length_entail_wit_5_split_goal_3 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (sorted_int_list_by 1 sorted_full_l ) ”
.

Definition by_length_entail_wit_5_split_goal_spatial := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (sorted_full_l: (@list Z)) (sorted_l_2: (@list Z)) (PreH1 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH2 : (arr_size_pre = (Zlength (sorted_full_l)))) (PreH3 : (0 <= arr_size_pre)) (PreH4 : (arr_size_pre <= arr_size_pre)) (PreH5 : (0 <= arr_size_pre)) (PreH6 : (arr_size_pre < INT_MAX)) (PreH7 : ((sublist (0) (arr_size_pre) (sorted_full_l)) = sorted_l_2)) (PreH8 : (sorted_int_list_by 1 sorted_l_2 )) (PreH9 : (Permutation input_l sorted_l_2 )) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (out_size = 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_entail_wit_6 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l 0 output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= 0) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - 0 )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 = out_size) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 0 output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - 0 )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - 0 )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= 0) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - 0 )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - 0 )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - 0 )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_7 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (k: Z) (sorted_l_2: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH27 : (out_size = (Zlength (output_rows_2)))) (PreH28 : (out_size = (Zlength (output_ptrs_2)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (((arr_size_pre - 1 ) - k ) < arr_size_pre) ” 
  &&  “ (0 <= ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (((arr_size_pre - 1 ) - k ) < arr_size_pre) ” 
  &&  “ (((arr_size_pre - 1 ) - k ) = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= (Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0))) ” 
  &&  “ ((Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)) <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.missing_i tmp ((arr_size_pre - 1 ) - k ) 0 arr_size_pre sorted_l )
  **  (((tmp + (((arr_size_pre - 1 ) - k ) * sizeof(INT) ) )) # Int  |-> (Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)))
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (k: Z) (sorted_l_2: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH27 : (out_size = (Zlength (output_rows_2)))) (PreH28 : (out_size = (Zlength (output_ptrs_2)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (IntArray.missing_i tmp ((arr_size_pre - 1 ) - k ) 0 arr_size_pre sorted_l_2 )
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (sorted_l: (@list Z)) ,
  “ ((Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)) = (Znth ((arr_size_pre - 1 ) - k ) sorted_l_2 0)) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (((arr_size_pre - 1 ) - k ) < arr_size_pre) ” 
  &&  “ (0 <= ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (((arr_size_pre - 1 ) - k ) < arr_size_pre) ” 
  &&  “ (INT_MIN <= (Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0))) ” 
  &&  “ ((Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)) <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) arr_size_pre )
  **  (IntArray.missing_i tmp ((arr_size_pre - 1 ) - k ) 0 arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_8 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l )) (PreH20 : (Permutation input_l sorted_l )) (PreH21 : (int_range_list_105 sorted_l )) (PreH22 : (digit_payloads_string_safe_105 )) (PreH23 : (0 <= k)) (PreH24 : (k < arr_size_pre)) (PreH25 : (0 <= ((arr_size_pre - 1 ) - k ))) (PreH26 : (((arr_size_pre - 1 ) - k ) < arr_size_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < arr_size_pre)) (PreH29 : (i = ((arr_size_pre - 1 ) - k ))) (PreH30 : (INT_MIN <= (Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)))) (PreH31 : ((Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)) <= INT_MAX)) (PreH32 : (output_state_105 LitMap sorted_l k output_rows_2 output_ptrs_2 )) (PreH33 : (out_size = (Zlength (output_rows_2)))) (PreH34 : (out_size = (Zlength (output_ptrs_2)))) (PreH35 : (0 <= out_size)) (PreH36 : (out_size <= k)) (PreH37 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.missing_i tmp i 0 arr_size_pre sorted_l )
  **  (((tmp + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (sorted_l) (0)))
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l_2: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= (Znth (i) (sorted_l) (0))) ” 
  &&  “ ((Znth (i) (sorted_l) (0)) <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ ((Znth (i) (sorted_l) (0)) = (Znth (i) (sorted_l_2) (0))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : ((Znth (i) (sorted_l) (0)) <= INT_MAX)) (PreH2 : ((Znth (i) (sorted_l) (0)) >= INT_MIN)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (arr_size_pre = (Zlength (sorted_l)))) (PreH20 : (problem_105_pre_z input_l )) (PreH21 : (sorted_int_list_by 1 sorted_l )) (PreH22 : (Permutation input_l sorted_l )) (PreH23 : (int_range_list_105 sorted_l )) (PreH24 : (digit_payloads_string_safe_105 )) (PreH25 : (0 <= k)) (PreH26 : (k < arr_size_pre)) (PreH27 : (0 <= ((arr_size_pre - 1 ) - k ))) (PreH28 : (((arr_size_pre - 1 ) - k ) < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= (Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)))) (PreH33 : ((Znth (((arr_size_pre - 1 ) - k )) (sorted_l) (0)) <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l k output_rows_2 output_ptrs_2 )) (PreH35 : (out_size = (Zlength (output_rows_2)))) (PreH36 : (out_size = (Zlength (output_ptrs_2)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.missing_i tmp i 0 arr_size_pre sorted_l )
  **  (((tmp + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (sorted_l) (0)))
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (sorted_l_2: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= (Znth (i) (sorted_l) (0))) ” 
  &&  “ ((Znth (i) (sorted_l) (0)) <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 k output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ ((Znth (i) (sorted_l) (0)) = (Znth (i) (sorted_l_2) (0))) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d > 9)) (PreH2 : (d >= 1)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH20 : (problem_105_pre_z input_l )) (PreH21 : (sorted_int_list_by 1 sorted_l_2 )) (PreH22 : (Permutation input_l sorted_l_2 )) (PreH23 : (int_range_list_105 sorted_l_2 )) (PreH24 : (digit_payloads_string_safe_105 )) (PreH25 : (0 <= k)) (PreH26 : (k < arr_size_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < arr_size_pre)) (PreH29 : (i = ((arr_size_pre - 1 ) - k ))) (PreH30 : (INT_MIN <= d)) (PreH31 : (d <= INT_MAX)) (PreH32 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH33 : (out_size = (Zlength (output_rows_2)))) (PreH34 : (out_size = (Zlength (output_ptrs_2)))) (PreH35 : (0 <= out_size)) (PreH36 : (out_size <= k)) (PreH37 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH38 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d > 9)) (PreH2 : (d >= 1)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (tmp <> 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH20 : (problem_105_pre_z input_l )) (PreH21 : (sorted_int_list_by 1 sorted_l_2 )) (PreH22 : (Permutation input_l sorted_l_2 )) (PreH23 : (int_range_list_105 sorted_l_2 )) (PreH24 : (digit_payloads_string_safe_105 )) (PreH25 : (0 <= k)) (PreH26 : (k < arr_size_pre)) (PreH27 : (0 <= i)) (PreH28 : (i < arr_size_pre)) (PreH29 : (i = ((arr_size_pre - 1 ) - k ))) (PreH30 : (INT_MIN <= d)) (PreH31 : (d <= INT_MAX)) (PreH32 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH33 : (out_size = (Zlength (output_rows_2)))) (PreH34 : (out_size = (Zlength (output_ptrs_2)))) (PreH35 : (0 <= out_size)) (PreH36 : (out_size <= k)) (PreH37 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH38 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_2 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d < 1)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k < arr_size_pre)) (PreH26 : (0 <= i)) (PreH27 : (i < arr_size_pre)) (PreH28 : (i = ((arr_size_pre - 1 ) - k ))) (PreH29 : (INT_MIN <= d)) (PreH30 : (d <= INT_MAX)) (PreH31 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH32 : (out_size = (Zlength (output_rows_2)))) (PreH33 : (out_size = (Zlength (output_ptrs_2)))) (PreH34 : (0 <= out_size)) (PreH35 : (out_size <= k)) (PreH36 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH37 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d < 1)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k < arr_size_pre)) (PreH26 : (0 <= i)) (PreH27 : (i < arr_size_pre)) (PreH28 : (i = ((arr_size_pre - 1 ) - k ))) (PreH29 : (INT_MIN <= d)) (PreH30 : (d <= INT_MAX)) (PreH31 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH32 : (out_size = (Zlength (output_rows_2)))) (PreH33 : (out_size = (Zlength (output_ptrs_2)))) (PreH34 : (0 <= out_size)) (PreH35 : (out_size <= k)) (PreH36 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH37 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_3 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l_2 )) (PreH30 : (Permutation input_l sorted_l_2 )) (PreH31 : (int_range_list_105 sorted_l_2 )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH41 : (out_size = (Zlength (output_rows_2)))) (PreH42 : (out_size = (Zlength (output_ptrs_2)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (nine) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l_2 )) (PreH30 : (Permutation input_l sorted_l_2 )) (PreH31 : (int_range_list_105 sorted_l_2 )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH41 : (out_size = (Zlength (output_rows_2)))) (PreH42 : (out_size = (Zlength (output_ptrs_2)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (nine) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_4 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l_2 )) (PreH30 : (Permutation input_l sorted_l_2 )) (PreH31 : (int_range_list_105 sorted_l_2 )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH41 : (out_size = (Zlength (output_rows_2)))) (PreH42 : (out_size = (Zlength (output_ptrs_2)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (eight) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l_2 )) (PreH30 : (Permutation input_l sorted_l_2 )) (PreH31 : (int_range_list_105 sorted_l_2 )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH41 : (out_size = (Zlength (output_rows_2)))) (PreH42 : (out_size = (Zlength (output_ptrs_2)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (eight) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_5 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 7)) (PreH2 : (d <> 6)) (PreH3 : (d <> 5)) (PreH4 : (d <> 4)) (PreH5 : (d <> 3)) (PreH6 : (d <> 2)) (PreH7 : (d <> 1)) (PreH8 : (d <= 9)) (PreH9 : (d >= 1)) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (arr_pre <> 0)) (PreH23 : (0 <= arr_size_pre)) (PreH24 : (arr_size_pre < INT_MAX)) (PreH25 : (arr_size_pre = (Zlength (input_l)))) (PreH26 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (sorted_int_list_by 1 sorted_l_2 )) (PreH29 : (Permutation input_l sorted_l_2 )) (PreH30 : (int_range_list_105 sorted_l_2 )) (PreH31 : (digit_payloads_string_safe_105 )) (PreH32 : (0 <= k)) (PreH33 : (k < arr_size_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < arr_size_pre)) (PreH36 : (i = ((arr_size_pre - 1 ) - k ))) (PreH37 : (INT_MIN <= d)) (PreH38 : (d <= INT_MAX)) (PreH39 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH40 : (out_size = (Zlength (output_rows_2)))) (PreH41 : (out_size = (Zlength (output_ptrs_2)))) (PreH42 : (0 <= out_size)) (PreH43 : (out_size <= k)) (PreH44 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH45 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (seven) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 7)) (PreH2 : (d <> 6)) (PreH3 : (d <> 5)) (PreH4 : (d <> 4)) (PreH5 : (d <> 3)) (PreH6 : (d <> 2)) (PreH7 : (d <> 1)) (PreH8 : (d <= 9)) (PreH9 : (d >= 1)) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (arr_pre <> 0)) (PreH23 : (0 <= arr_size_pre)) (PreH24 : (arr_size_pre < INT_MAX)) (PreH25 : (arr_size_pre = (Zlength (input_l)))) (PreH26 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (sorted_int_list_by 1 sorted_l_2 )) (PreH29 : (Permutation input_l sorted_l_2 )) (PreH30 : (int_range_list_105 sorted_l_2 )) (PreH31 : (digit_payloads_string_safe_105 )) (PreH32 : (0 <= k)) (PreH33 : (k < arr_size_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < arr_size_pre)) (PreH36 : (i = ((arr_size_pre - 1 ) - k ))) (PreH37 : (INT_MIN <= d)) (PreH38 : (d <= INT_MAX)) (PreH39 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH40 : (out_size = (Zlength (output_rows_2)))) (PreH41 : (out_size = (Zlength (output_ptrs_2)))) (PreH42 : (0 <= out_size)) (PreH43 : (out_size <= k)) (PreH44 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH45 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (seven) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_6 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 6)) (PreH2 : (d <> 5)) (PreH3 : (d <> 4)) (PreH4 : (d <> 3)) (PreH5 : (d <> 2)) (PreH6 : (d <> 1)) (PreH7 : (d <= 9)) (PreH8 : (d >= 1)) (PreH9 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH10 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH11 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH12 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH13 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH14 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH15 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH16 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH17 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (tmp <> 0)) (PreH21 : (arr_pre <> 0)) (PreH22 : (0 <= arr_size_pre)) (PreH23 : (arr_size_pre < INT_MAX)) (PreH24 : (arr_size_pre = (Zlength (input_l)))) (PreH25 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH26 : (problem_105_pre_z input_l )) (PreH27 : (sorted_int_list_by 1 sorted_l_2 )) (PreH28 : (Permutation input_l sorted_l_2 )) (PreH29 : (int_range_list_105 sorted_l_2 )) (PreH30 : (digit_payloads_string_safe_105 )) (PreH31 : (0 <= k)) (PreH32 : (k < arr_size_pre)) (PreH33 : (0 <= i)) (PreH34 : (i < arr_size_pre)) (PreH35 : (i = ((arr_size_pre - 1 ) - k ))) (PreH36 : (INT_MIN <= d)) (PreH37 : (d <= INT_MAX)) (PreH38 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH39 : (out_size = (Zlength (output_rows_2)))) (PreH40 : (out_size = (Zlength (output_ptrs_2)))) (PreH41 : (0 <= out_size)) (PreH42 : (out_size <= k)) (PreH43 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH44 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (six) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 6)) (PreH2 : (d <> 5)) (PreH3 : (d <> 4)) (PreH4 : (d <> 3)) (PreH5 : (d <> 2)) (PreH6 : (d <> 1)) (PreH7 : (d <= 9)) (PreH8 : (d >= 1)) (PreH9 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH10 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH11 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH12 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH13 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH14 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH15 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH16 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH17 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (tmp <> 0)) (PreH21 : (arr_pre <> 0)) (PreH22 : (0 <= arr_size_pre)) (PreH23 : (arr_size_pre < INT_MAX)) (PreH24 : (arr_size_pre = (Zlength (input_l)))) (PreH25 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH26 : (problem_105_pre_z input_l )) (PreH27 : (sorted_int_list_by 1 sorted_l_2 )) (PreH28 : (Permutation input_l sorted_l_2 )) (PreH29 : (int_range_list_105 sorted_l_2 )) (PreH30 : (digit_payloads_string_safe_105 )) (PreH31 : (0 <= k)) (PreH32 : (k < arr_size_pre)) (PreH33 : (0 <= i)) (PreH34 : (i < arr_size_pre)) (PreH35 : (i = ((arr_size_pre - 1 ) - k ))) (PreH36 : (INT_MIN <= d)) (PreH37 : (d <= INT_MAX)) (PreH38 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH39 : (out_size = (Zlength (output_rows_2)))) (PreH40 : (out_size = (Zlength (output_ptrs_2)))) (PreH41 : (0 <= out_size)) (PreH42 : (out_size <= k)) (PreH43 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH44 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (six) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_7 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 5)) (PreH2 : (d <> 4)) (PreH3 : (d <> 3)) (PreH4 : (d <> 2)) (PreH5 : (d <> 1)) (PreH6 : (d <= 9)) (PreH7 : (d >= 1)) (PreH8 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH9 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH10 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH11 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH12 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH13 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH14 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH15 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH16 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (tmp <> 0)) (PreH20 : (arr_pre <> 0)) (PreH21 : (0 <= arr_size_pre)) (PreH22 : (arr_size_pre < INT_MAX)) (PreH23 : (arr_size_pre = (Zlength (input_l)))) (PreH24 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH25 : (problem_105_pre_z input_l )) (PreH26 : (sorted_int_list_by 1 sorted_l_2 )) (PreH27 : (Permutation input_l sorted_l_2 )) (PreH28 : (int_range_list_105 sorted_l_2 )) (PreH29 : (digit_payloads_string_safe_105 )) (PreH30 : (0 <= k)) (PreH31 : (k < arr_size_pre)) (PreH32 : (0 <= i)) (PreH33 : (i < arr_size_pre)) (PreH34 : (i = ((arr_size_pre - 1 ) - k ))) (PreH35 : (INT_MIN <= d)) (PreH36 : (d <= INT_MAX)) (PreH37 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH38 : (out_size = (Zlength (output_rows_2)))) (PreH39 : (out_size = (Zlength (output_ptrs_2)))) (PreH40 : (0 <= out_size)) (PreH41 : (out_size <= k)) (PreH42 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH43 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (five) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 5)) (PreH2 : (d <> 4)) (PreH3 : (d <> 3)) (PreH4 : (d <> 2)) (PreH5 : (d <> 1)) (PreH6 : (d <= 9)) (PreH7 : (d >= 1)) (PreH8 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH9 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH10 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH11 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH12 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH13 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH14 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH15 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH16 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (tmp <> 0)) (PreH20 : (arr_pre <> 0)) (PreH21 : (0 <= arr_size_pre)) (PreH22 : (arr_size_pre < INT_MAX)) (PreH23 : (arr_size_pre = (Zlength (input_l)))) (PreH24 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH25 : (problem_105_pre_z input_l )) (PreH26 : (sorted_int_list_by 1 sorted_l_2 )) (PreH27 : (Permutation input_l sorted_l_2 )) (PreH28 : (int_range_list_105 sorted_l_2 )) (PreH29 : (digit_payloads_string_safe_105 )) (PreH30 : (0 <= k)) (PreH31 : (k < arr_size_pre)) (PreH32 : (0 <= i)) (PreH33 : (i < arr_size_pre)) (PreH34 : (i = ((arr_size_pre - 1 ) - k ))) (PreH35 : (INT_MIN <= d)) (PreH36 : (d <= INT_MAX)) (PreH37 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH38 : (out_size = (Zlength (output_rows_2)))) (PreH39 : (out_size = (Zlength (output_ptrs_2)))) (PreH40 : (0 <= out_size)) (PreH41 : (out_size <= k)) (PreH42 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH43 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (five) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_8 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 4)) (PreH2 : (d <> 3)) (PreH3 : (d <> 2)) (PreH4 : (d <> 1)) (PreH5 : (d <= 9)) (PreH6 : (d >= 1)) (PreH7 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH8 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH9 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH10 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH11 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH12 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH13 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH14 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH15 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (tmp <> 0)) (PreH19 : (arr_pre <> 0)) (PreH20 : (0 <= arr_size_pre)) (PreH21 : (arr_size_pre < INT_MAX)) (PreH22 : (arr_size_pre = (Zlength (input_l)))) (PreH23 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH24 : (problem_105_pre_z input_l )) (PreH25 : (sorted_int_list_by 1 sorted_l_2 )) (PreH26 : (Permutation input_l sorted_l_2 )) (PreH27 : (int_range_list_105 sorted_l_2 )) (PreH28 : (digit_payloads_string_safe_105 )) (PreH29 : (0 <= k)) (PreH30 : (k < arr_size_pre)) (PreH31 : (0 <= i)) (PreH32 : (i < arr_size_pre)) (PreH33 : (i = ((arr_size_pre - 1 ) - k ))) (PreH34 : (INT_MIN <= d)) (PreH35 : (d <= INT_MAX)) (PreH36 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH37 : (out_size = (Zlength (output_rows_2)))) (PreH38 : (out_size = (Zlength (output_ptrs_2)))) (PreH39 : (0 <= out_size)) (PreH40 : (out_size <= k)) (PreH41 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH42 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (four) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 4)) (PreH2 : (d <> 3)) (PreH3 : (d <> 2)) (PreH4 : (d <> 1)) (PreH5 : (d <= 9)) (PreH6 : (d >= 1)) (PreH7 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH8 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH9 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH10 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH11 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH12 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH13 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH14 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH15 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (tmp <> 0)) (PreH19 : (arr_pre <> 0)) (PreH20 : (0 <= arr_size_pre)) (PreH21 : (arr_size_pre < INT_MAX)) (PreH22 : (arr_size_pre = (Zlength (input_l)))) (PreH23 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH24 : (problem_105_pre_z input_l )) (PreH25 : (sorted_int_list_by 1 sorted_l_2 )) (PreH26 : (Permutation input_l sorted_l_2 )) (PreH27 : (int_range_list_105 sorted_l_2 )) (PreH28 : (digit_payloads_string_safe_105 )) (PreH29 : (0 <= k)) (PreH30 : (k < arr_size_pre)) (PreH31 : (0 <= i)) (PreH32 : (i < arr_size_pre)) (PreH33 : (i = ((arr_size_pre - 1 ) - k ))) (PreH34 : (INT_MIN <= d)) (PreH35 : (d <= INT_MAX)) (PreH36 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH37 : (out_size = (Zlength (output_rows_2)))) (PreH38 : (out_size = (Zlength (output_ptrs_2)))) (PreH39 : (0 <= out_size)) (PreH40 : (out_size <= k)) (PreH41 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH42 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (four) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_9 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 3)) (PreH2 : (d <> 2)) (PreH3 : (d <> 1)) (PreH4 : (d <= 9)) (PreH5 : (d >= 1)) (PreH6 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH7 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH8 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH9 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH10 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH11 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH12 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH13 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH14 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (tmp <> 0)) (PreH18 : (arr_pre <> 0)) (PreH19 : (0 <= arr_size_pre)) (PreH20 : (arr_size_pre < INT_MAX)) (PreH21 : (arr_size_pre = (Zlength (input_l)))) (PreH22 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH23 : (problem_105_pre_z input_l )) (PreH24 : (sorted_int_list_by 1 sorted_l_2 )) (PreH25 : (Permutation input_l sorted_l_2 )) (PreH26 : (int_range_list_105 sorted_l_2 )) (PreH27 : (digit_payloads_string_safe_105 )) (PreH28 : (0 <= k)) (PreH29 : (k < arr_size_pre)) (PreH30 : (0 <= i)) (PreH31 : (i < arr_size_pre)) (PreH32 : (i = ((arr_size_pre - 1 ) - k ))) (PreH33 : (INT_MIN <= d)) (PreH34 : (d <= INT_MAX)) (PreH35 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH36 : (out_size = (Zlength (output_rows_2)))) (PreH37 : (out_size = (Zlength (output_ptrs_2)))) (PreH38 : (0 <= out_size)) (PreH39 : (out_size <= k)) (PreH40 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH41 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (three) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 3)) (PreH2 : (d <> 2)) (PreH3 : (d <> 1)) (PreH4 : (d <= 9)) (PreH5 : (d >= 1)) (PreH6 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH7 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH8 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH9 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH10 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH11 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH12 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH13 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH14 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (tmp <> 0)) (PreH18 : (arr_pre <> 0)) (PreH19 : (0 <= arr_size_pre)) (PreH20 : (arr_size_pre < INT_MAX)) (PreH21 : (arr_size_pre = (Zlength (input_l)))) (PreH22 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH23 : (problem_105_pre_z input_l )) (PreH24 : (sorted_int_list_by 1 sorted_l_2 )) (PreH25 : (Permutation input_l sorted_l_2 )) (PreH26 : (int_range_list_105 sorted_l_2 )) (PreH27 : (digit_payloads_string_safe_105 )) (PreH28 : (0 <= k)) (PreH29 : (k < arr_size_pre)) (PreH30 : (0 <= i)) (PreH31 : (i < arr_size_pre)) (PreH32 : (i = ((arr_size_pre - 1 ) - k ))) (PreH33 : (INT_MIN <= d)) (PreH34 : (d <= INT_MAX)) (PreH35 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH36 : (out_size = (Zlength (output_rows_2)))) (PreH37 : (out_size = (Zlength (output_ptrs_2)))) (PreH38 : (0 <= out_size)) (PreH39 : (out_size <= k)) (PreH40 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH41 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (three) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_10 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 2)) (PreH2 : (d <> 1)) (PreH3 : (d <= 9)) (PreH4 : (d >= 1)) (PreH5 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH6 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH7 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH8 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH9 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH10 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH11 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH12 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH13 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (tmp <> 0)) (PreH17 : (arr_pre <> 0)) (PreH18 : (0 <= arr_size_pre)) (PreH19 : (arr_size_pre < INT_MAX)) (PreH20 : (arr_size_pre = (Zlength (input_l)))) (PreH21 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH22 : (problem_105_pre_z input_l )) (PreH23 : (sorted_int_list_by 1 sorted_l_2 )) (PreH24 : (Permutation input_l sorted_l_2 )) (PreH25 : (int_range_list_105 sorted_l_2 )) (PreH26 : (digit_payloads_string_safe_105 )) (PreH27 : (0 <= k)) (PreH28 : (k < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= d)) (PreH33 : (d <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH35 : (out_size = (Zlength (output_rows_2)))) (PreH36 : (out_size = (Zlength (output_ptrs_2)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH40 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (two) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 2)) (PreH2 : (d <> 1)) (PreH3 : (d <= 9)) (PreH4 : (d >= 1)) (PreH5 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH6 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH7 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH8 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH9 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH10 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH11 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH12 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH13 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (tmp <> 0)) (PreH17 : (arr_pre <> 0)) (PreH18 : (0 <= arr_size_pre)) (PreH19 : (arr_size_pre < INT_MAX)) (PreH20 : (arr_size_pre = (Zlength (input_l)))) (PreH21 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH22 : (problem_105_pre_z input_l )) (PreH23 : (sorted_int_list_by 1 sorted_l_2 )) (PreH24 : (Permutation input_l sorted_l_2 )) (PreH25 : (int_range_list_105 sorted_l_2 )) (PreH26 : (digit_payloads_string_safe_105 )) (PreH27 : (0 <= k)) (PreH28 : (k < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= d)) (PreH33 : (d <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH35 : (out_size = (Zlength (output_rows_2)))) (PreH36 : (out_size = (Zlength (output_ptrs_2)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH40 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (two) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_9_11 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 1)) (PreH2 : (d <= 9)) (PreH3 : (d >= 1)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (tmp <> 0)) (PreH16 : (arr_pre <> 0)) (PreH17 : (0 <= arr_size_pre)) (PreH18 : (arr_size_pre < INT_MAX)) (PreH19 : (arr_size_pre = (Zlength (input_l)))) (PreH20 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH21 : (problem_105_pre_z input_l )) (PreH22 : (sorted_int_list_by 1 sorted_l_2 )) (PreH23 : (Permutation input_l sorted_l_2 )) (PreH24 : (int_range_list_105 sorted_l_2 )) (PreH25 : (digit_payloads_string_safe_105 )) (PreH26 : (0 <= k)) (PreH27 : (k < arr_size_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < arr_size_pre)) (PreH30 : (i = ((arr_size_pre - 1 ) - k ))) (PreH31 : (INT_MIN <= d)) (PreH32 : (d <= INT_MAX)) (PreH33 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH34 : (out_size = (Zlength (output_rows_2)))) (PreH35 : (out_size = (Zlength (output_ptrs_2)))) (PreH36 : (0 <= out_size)) (PreH37 : (out_size <= k)) (PreH38 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH39 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (one) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 1)) (PreH2 : (d <= 9)) (PreH3 : (d >= 1)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (tmp <> 0)) (PreH16 : (arr_pre <> 0)) (PreH17 : (0 <= arr_size_pre)) (PreH18 : (arr_size_pre < INT_MAX)) (PreH19 : (arr_size_pre = (Zlength (input_l)))) (PreH20 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH21 : (problem_105_pre_z input_l )) (PreH22 : (sorted_int_list_by 1 sorted_l_2 )) (PreH23 : (Permutation input_l sorted_l_2 )) (PreH24 : (int_range_list_105 sorted_l_2 )) (PreH25 : (digit_payloads_string_safe_105 )) (PreH26 : (0 <= k)) (PreH27 : (k < arr_size_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < arr_size_pre)) (PreH30 : (i = ((arr_size_pre - 1 ) - k ))) (PreH31 : (INT_MIN <= d)) (PreH32 : (d <= INT_MAX)) (PreH33 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH34 : (out_size = (Zlength (output_rows_2)))) (PreH35 : (out_size = (Zlength (output_ptrs_2)))) (PreH36 : (0 <= out_size)) (PreH37 : (out_size <= k)) (PreH38 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) (PreH39 : (d = (Znth (i) (sorted_l_2) (0)))) ,
  (PtrArray.seg data 0 ((Zlength (output_ptrs_2)) + 1 ) (app (output_ptrs_2) ((cons (one) ((@nil Z))))) )
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (PtrArray.undef_seg data (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_10 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (k: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l_2 )) (PreH20 : (Permutation input_l sorted_l_2 )) (PreH21 : (int_range_list_105 sorted_l_2 )) (PreH22 : (digit_payloads_string_safe_105 )) (PreH23 : (0 <= k)) (PreH24 : (k < arr_size_pre)) (PreH25 : (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows_2 output_ptrs_2 )) (PreH26 : (out_size = (Zlength (output_rows_2)))) (PreH27 : (out_size = (Zlength (output_ptrs_2)))) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= (k + 1 ))) (PreH30 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l (k + 1 ) output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (k: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l_2 )) (PreH20 : (Permutation input_l sorted_l_2 )) (PreH21 : (int_range_list_105 sorted_l_2 )) (PreH22 : (digit_payloads_string_safe_105 )) (PreH23 : (0 <= k)) (PreH24 : (k < arr_size_pre)) (PreH25 : (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows_2 output_ptrs_2 )) (PreH26 : (out_size = (Zlength (output_rows_2)))) (PreH27 : (out_size = (Zlength (output_ptrs_2)))) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= (k + 1 ))) (PreH30 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) ,
  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= arr_size_pre) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 (k + 1 ) output_rows (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre))))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (k + 1 )) ”
  &&  (PtrArray.seg data 0 (Zlength ((digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)))) (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - (k + 1 ) )) (arr_size_pre)) )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_11 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (k: Z) (sorted_l_2: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k >= arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH27 : (out_size = (Zlength (output_rows_2)))) (PreH28 : (out_size = (Zlength (output_ptrs_2)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l_2 )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (output_state_105 LitMap sorted_l arr_size_pre output_rows output_ptrs ) ” 
  &&  “ (problem_105_spec_z_of_output_state input_l sorted_l output_rows LitMap output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= arr_size_pre) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (out_size: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (k: Z) (sorted_l_2: (@list Z)) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (k >= arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (sorted_int_list_by 1 sorted_l_2 )) (PreH21 : (Permutation input_l sorted_l_2 )) (PreH22 : (int_range_list_105 sorted_l_2 )) (PreH23 : (digit_payloads_string_safe_105 )) (PreH24 : (0 <= k)) (PreH25 : (k <= arr_size_pre)) (PreH26 : (output_state_105 LitMap sorted_l_2 k output_rows_2 output_ptrs_2 )) (PreH27 : (out_size = (Zlength (output_rows_2)))) (PreH28 : (out_size = (Zlength (output_ptrs_2)))) (PreH29 : (0 <= out_size)) (PreH30 : (out_size <= k)) (PreH31 : (output_ptrs_2 = (digit_ptrs_between_105 (LitMap) (sorted_l_2) ((arr_size_pre - k )) (arr_size_pre)))) ,
  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l_2))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l_2 ) ” 
  &&  “ (Permutation input_l sorted_l_2 ) ” 
  &&  “ (int_range_list_105 sorted_l_2 ) ” 
  &&  “ (output_state_105 LitMap sorted_l_2 arr_size_pre output_rows output_ptrs ) ” 
  &&  “ (problem_105_spec_z_of_output_state input_l sorted_l_2 output_rows LitMap output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= arr_size_pre) ”
  &&  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_entail_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l_2)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l_2 )) (PreH20 : (Permutation input_l sorted_l_2 )) (PreH21 : (int_range_list_105 sorted_l_2 )) (PreH22 : (output_state_105 LitMap sorted_l_2 arr_size_pre output_rows_2 output_ptrs_2 )) (PreH23 : (problem_105_spec_z_of_output_state input_l sorted_l_2 output_rows_2 LitMap output_ptrs_2 )) (PreH24 : (out_size = (Zlength (output_rows_2)))) (PreH25 : (out_size = (Zlength (output_ptrs_2)))) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= arr_size_pre)) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (sorted_l: (@list Z)) ,
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (output_state_105 LitMap sorted_l arr_size_pre output_rows output_ptrs ) ” 
  &&  “ (problem_105_spec_z_of_output_state input_l sorted_l output_rows LitMap output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= arr_size_pre) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_return_wit_1 := 
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data_2: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data_2 <> 0)) (PreH12 : (arr_pre <> 0)) (PreH13 : (0 <= arr_size_pre)) (PreH14 : (arr_size_pre < INT_MAX)) (PreH15 : (arr_size_pre = (Zlength (input_l)))) (PreH16 : (arr_size_pre = (Zlength (sorted_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (sorted_int_list_by 1 sorted_l )) (PreH19 : (Permutation input_l sorted_l )) (PreH20 : (int_range_list_105 sorted_l )) (PreH21 : (output_state_105 LitMap sorted_l arr_size_pre output_rows_2 output_ptrs_2 )) (PreH22 : (problem_105_spec_z_of_output_state input_l sorted_l output_rows_2 LitMap output_ptrs_2 )) (PreH23 : (out_size = (Zlength (output_rows_2)))) (PreH24 : (out_size = (Zlength (output_ptrs_2)))) (PreH25 : (0 <= out_size)) (PreH26 : (out_size <= arr_size_pre)) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data_2 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= arr_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (problem_105_spec_z input_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
) \/
(
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data_2: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data_2 <> 0)) (PreH12 : (arr_pre <> 0)) (PreH13 : (0 <= arr_size_pre)) (PreH14 : (arr_size_pre < INT_MAX)) (PreH15 : (arr_size_pre = (Zlength (input_l)))) (PreH16 : (arr_size_pre = (Zlength (sorted_l)))) (PreH17 : (problem_105_pre_z input_l )) (PreH18 : (sorted_int_list_by 1 sorted_l )) (PreH19 : (Permutation input_l sorted_l )) (PreH20 : (int_range_list_105 sorted_l )) (PreH21 : (output_state_105 LitMap sorted_l arr_size_pre output_rows_2 output_ptrs_2 )) (PreH22 : (problem_105_spec_z_of_output_state input_l sorted_l output_rows_2 LitMap output_ptrs_2 )) (PreH23 : (out_size = (Zlength (output_rows_2)))) (PreH24 : (out_size = (Zlength (output_ptrs_2)))) (PreH25 : (0 <= out_size)) (PreH26 : (out_size <= arr_size_pre)) ,
  (PtrArray.seg data_2 0 (Zlength (output_ptrs_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 (Zlength (output_ptrs_2)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) <= arr_size_pre) ” 
  &&  “ ((Zlength (output_rows)) = (Zlength (output_ptrs))) ” 
  &&  “ (problem_105_spec_z input_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
).

Definition by_length_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (arr_pre <> 0)) (PreH11 : (0 <= arr_size_pre)) (PreH12 : (arr_size_pre < INT_MAX)) (PreH13 : (arr_size_pre = (Zlength (input_l)))) (PreH14 : (problem_105_pre_z input_l )) (PreH15 : (digit_payloads_string_safe_105 )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_2_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (arr_pre <> 0)) (PreH12 : (0 <= arr_size_pre)) (PreH13 : (arr_size_pre < INT_MAX)) (PreH14 : (arr_size_pre = (Zlength (input_l)))) (PreH15 : (problem_105_pre_z input_l )) (PreH16 : (digit_payloads_string_safe_105 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ”
.

Definition by_length_partial_solve_wit_2_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (arr_pre <> 0)) (PreH12 : (0 <= arr_size_pre)) (PreH13 : (arr_size_pre < INT_MAX)) (PreH14 : (arr_size_pre = (Zlength (input_l)))) (PreH15 : (problem_105_pre_z input_l )) (PreH16 : (digit_payloads_string_safe_105 )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_2 := by_length_partial_solve_wit_2_pure -> by_length_partial_solve_wit_2_aux.

Definition by_length_partial_solve_wit_3_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (arr_pre <> 0)) (PreH13 : (0 <= arr_size_pre)) (PreH14 : (arr_size_pre < INT_MAX)) (PreH15 : (arr_size_pre = (Zlength (input_l)))) (PreH16 : (problem_105_pre_z input_l )) (PreH17 : (digit_payloads_string_safe_105 )) ,
  ((( &( "tmp" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ”
.

Definition by_length_partial_solve_wit_3_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH4 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH5 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH6 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH7 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH8 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH9 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH10 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH11 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH12 : (arr_pre <> 0)) (PreH13 : (0 <= arr_size_pre)) (PreH14 : (arr_size_pre < INT_MAX)) (PreH15 : (arr_size_pre = (Zlength (input_l)))) (PreH16 : (problem_105_pre_z input_l )) (PreH17 : (digit_payloads_string_safe_105 )) ,
  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (arr_size_pre >= 0) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (PtrArray.undef_full retval_2 arr_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_3 := by_length_partial_solve_wit_3_pure -> by_length_partial_solve_wit_3_aux.

Definition by_length_partial_solve_wit_4 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (i = (Zlength (tmp_l))) ” 
  &&  “ (tmp_l = (copy_prefix_105 (input_l) (i))) ”
  &&  (((arr_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i arr_pre i 0 arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_5 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (tmp_l: (@list Z)) (i: Z) (out_size: Z) (tmp: Z) (data: Z) (out: Z) (nine: Z) (eight: Z) (seven: Z) (six: Z) (five: Z) (four: Z) (three: Z) (two: Z) (one: Z) (PreH1 : (i < arr_size_pre)) (PreH2 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH3 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH4 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH5 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH6 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH7 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH8 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH9 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH10 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (tmp <> 0)) (PreH14 : (out_size = 0)) (PreH15 : (arr_pre <> 0)) (PreH16 : (0 <= arr_size_pre)) (PreH17 : (arr_size_pre < INT_MAX)) (PreH18 : (arr_size_pre = (Zlength (input_l)))) (PreH19 : (problem_105_pre_z input_l )) (PreH20 : (digit_payloads_string_safe_105 )) (PreH21 : (0 <= i)) (PreH22 : (i <= arr_size_pre)) (PreH23 : (i = (Zlength (tmp_l)))) (PreH24 : (tmp_l = (copy_prefix_105 (input_l) (i)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (IntArray.undef_seg tmp i arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (i < arr_size_pre) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= arr_size_pre) ” 
  &&  “ (i = (Zlength (tmp_l))) ” 
  &&  “ (tmp_l = (copy_prefix_105 (input_l) (i))) ”
  &&  (((tmp + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg tmp (i + 1 ) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 i tmp_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_6_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (digit_payloads_string_safe_105 )) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> arr_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (tmp <> 0) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre <= arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ”
.

Definition by_length_partial_solve_wit_6_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (out_size = 0)) (PreH14 : (arr_pre <> 0)) (PreH15 : (0 <= arr_size_pre)) (PreH16 : (arr_size_pre < INT_MAX)) (PreH17 : (arr_size_pre = (Zlength (input_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (digit_payloads_string_safe_105 )) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (tmp <> 0) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre <= arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (out_size = 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ”
  &&  (IntArray.seg tmp 0 arr_size_pre input_l )
  **  (IntArray.undef_seg tmp arr_size_pre arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (PtrArray.undef_full data arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_6 := by_length_partial_solve_wit_6_pure -> by_length_partial_solve_wit_6_aux.

Definition by_length_partial_solve_wit_7 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 1)) (PreH2 : (d <= 9)) (PreH3 : (d >= 1)) (PreH4 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH5 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH6 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH7 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH8 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH9 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH10 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH11 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH12 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (tmp <> 0)) (PreH16 : (arr_pre <> 0)) (PreH17 : (0 <= arr_size_pre)) (PreH18 : (arr_size_pre < INT_MAX)) (PreH19 : (arr_size_pre = (Zlength (input_l)))) (PreH20 : (arr_size_pre = (Zlength (sorted_l)))) (PreH21 : (problem_105_pre_z input_l )) (PreH22 : (sorted_int_list_by 1 sorted_l )) (PreH23 : (Permutation input_l sorted_l )) (PreH24 : (int_range_list_105 sorted_l )) (PreH25 : (digit_payloads_string_safe_105 )) (PreH26 : (0 <= k)) (PreH27 : (k < arr_size_pre)) (PreH28 : (0 <= i)) (PreH29 : (i < arr_size_pre)) (PreH30 : (i = ((arr_size_pre - 1 ) - k ))) (PreH31 : (INT_MIN <= d)) (PreH32 : (d <= INT_MAX)) (PreH33 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH34 : (out_size = (Zlength (output_rows)))) (PreH35 : (out_size = (Zlength (output_ptrs)))) (PreH36 : (0 <= out_size)) (PreH37 : (out_size <= k)) (PreH38 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH39 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_8 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 2)) (PreH2 : (d <> 1)) (PreH3 : (d <= 9)) (PreH4 : (d >= 1)) (PreH5 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH6 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH7 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH8 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH9 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH10 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH11 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH12 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH13 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (tmp <> 0)) (PreH17 : (arr_pre <> 0)) (PreH18 : (0 <= arr_size_pre)) (PreH19 : (arr_size_pre < INT_MAX)) (PreH20 : (arr_size_pre = (Zlength (input_l)))) (PreH21 : (arr_size_pre = (Zlength (sorted_l)))) (PreH22 : (problem_105_pre_z input_l )) (PreH23 : (sorted_int_list_by 1 sorted_l )) (PreH24 : (Permutation input_l sorted_l )) (PreH25 : (int_range_list_105 sorted_l )) (PreH26 : (digit_payloads_string_safe_105 )) (PreH27 : (0 <= k)) (PreH28 : (k < arr_size_pre)) (PreH29 : (0 <= i)) (PreH30 : (i < arr_size_pre)) (PreH31 : (i = ((arr_size_pre - 1 ) - k ))) (PreH32 : (INT_MIN <= d)) (PreH33 : (d <= INT_MAX)) (PreH34 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH35 : (out_size = (Zlength (output_rows)))) (PreH36 : (out_size = (Zlength (output_ptrs)))) (PreH37 : (0 <= out_size)) (PreH38 : (out_size <= k)) (PreH39 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH40 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_9 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 3)) (PreH2 : (d <> 2)) (PreH3 : (d <> 1)) (PreH4 : (d <= 9)) (PreH5 : (d >= 1)) (PreH6 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH7 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH8 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH9 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH10 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH11 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH12 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH13 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH14 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (tmp <> 0)) (PreH18 : (arr_pre <> 0)) (PreH19 : (0 <= arr_size_pre)) (PreH20 : (arr_size_pre < INT_MAX)) (PreH21 : (arr_size_pre = (Zlength (input_l)))) (PreH22 : (arr_size_pre = (Zlength (sorted_l)))) (PreH23 : (problem_105_pre_z input_l )) (PreH24 : (sorted_int_list_by 1 sorted_l )) (PreH25 : (Permutation input_l sorted_l )) (PreH26 : (int_range_list_105 sorted_l )) (PreH27 : (digit_payloads_string_safe_105 )) (PreH28 : (0 <= k)) (PreH29 : (k < arr_size_pre)) (PreH30 : (0 <= i)) (PreH31 : (i < arr_size_pre)) (PreH32 : (i = ((arr_size_pre - 1 ) - k ))) (PreH33 : (INT_MIN <= d)) (PreH34 : (d <= INT_MAX)) (PreH35 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH36 : (out_size = (Zlength (output_rows)))) (PreH37 : (out_size = (Zlength (output_ptrs)))) (PreH38 : (0 <= out_size)) (PreH39 : (out_size <= k)) (PreH40 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH41 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_10 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 4)) (PreH2 : (d <> 3)) (PreH3 : (d <> 2)) (PreH4 : (d <> 1)) (PreH5 : (d <= 9)) (PreH6 : (d >= 1)) (PreH7 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH8 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH9 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH10 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH11 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH12 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH13 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH14 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH15 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (tmp <> 0)) (PreH19 : (arr_pre <> 0)) (PreH20 : (0 <= arr_size_pre)) (PreH21 : (arr_size_pre < INT_MAX)) (PreH22 : (arr_size_pre = (Zlength (input_l)))) (PreH23 : (arr_size_pre = (Zlength (sorted_l)))) (PreH24 : (problem_105_pre_z input_l )) (PreH25 : (sorted_int_list_by 1 sorted_l )) (PreH26 : (Permutation input_l sorted_l )) (PreH27 : (int_range_list_105 sorted_l )) (PreH28 : (digit_payloads_string_safe_105 )) (PreH29 : (0 <= k)) (PreH30 : (k < arr_size_pre)) (PreH31 : (0 <= i)) (PreH32 : (i < arr_size_pre)) (PreH33 : (i = ((arr_size_pre - 1 ) - k ))) (PreH34 : (INT_MIN <= d)) (PreH35 : (d <= INT_MAX)) (PreH36 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH37 : (out_size = (Zlength (output_rows)))) (PreH38 : (out_size = (Zlength (output_ptrs)))) (PreH39 : (0 <= out_size)) (PreH40 : (out_size <= k)) (PreH41 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH42 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_11 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 5)) (PreH2 : (d <> 4)) (PreH3 : (d <> 3)) (PreH4 : (d <> 2)) (PreH5 : (d <> 1)) (PreH6 : (d <= 9)) (PreH7 : (d >= 1)) (PreH8 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH9 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH10 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH11 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH12 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH13 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH14 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH15 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH16 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (tmp <> 0)) (PreH20 : (arr_pre <> 0)) (PreH21 : (0 <= arr_size_pre)) (PreH22 : (arr_size_pre < INT_MAX)) (PreH23 : (arr_size_pre = (Zlength (input_l)))) (PreH24 : (arr_size_pre = (Zlength (sorted_l)))) (PreH25 : (problem_105_pre_z input_l )) (PreH26 : (sorted_int_list_by 1 sorted_l )) (PreH27 : (Permutation input_l sorted_l )) (PreH28 : (int_range_list_105 sorted_l )) (PreH29 : (digit_payloads_string_safe_105 )) (PreH30 : (0 <= k)) (PreH31 : (k < arr_size_pre)) (PreH32 : (0 <= i)) (PreH33 : (i < arr_size_pre)) (PreH34 : (i = ((arr_size_pre - 1 ) - k ))) (PreH35 : (INT_MIN <= d)) (PreH36 : (d <= INT_MAX)) (PreH37 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH38 : (out_size = (Zlength (output_rows)))) (PreH39 : (out_size = (Zlength (output_ptrs)))) (PreH40 : (0 <= out_size)) (PreH41 : (out_size <= k)) (PreH42 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH43 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 5) ” 
  &&  “ (d <> 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_12 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 6)) (PreH2 : (d <> 5)) (PreH3 : (d <> 4)) (PreH4 : (d <> 3)) (PreH5 : (d <> 2)) (PreH6 : (d <> 1)) (PreH7 : (d <= 9)) (PreH8 : (d >= 1)) (PreH9 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH10 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH11 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH12 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH13 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH14 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH15 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH16 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH17 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (tmp <> 0)) (PreH21 : (arr_pre <> 0)) (PreH22 : (0 <= arr_size_pre)) (PreH23 : (arr_size_pre < INT_MAX)) (PreH24 : (arr_size_pre = (Zlength (input_l)))) (PreH25 : (arr_size_pre = (Zlength (sorted_l)))) (PreH26 : (problem_105_pre_z input_l )) (PreH27 : (sorted_int_list_by 1 sorted_l )) (PreH28 : (Permutation input_l sorted_l )) (PreH29 : (int_range_list_105 sorted_l )) (PreH30 : (digit_payloads_string_safe_105 )) (PreH31 : (0 <= k)) (PreH32 : (k < arr_size_pre)) (PreH33 : (0 <= i)) (PreH34 : (i < arr_size_pre)) (PreH35 : (i = ((arr_size_pre - 1 ) - k ))) (PreH36 : (INT_MIN <= d)) (PreH37 : (d <= INT_MAX)) (PreH38 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH39 : (out_size = (Zlength (output_rows)))) (PreH40 : (out_size = (Zlength (output_ptrs)))) (PreH41 : (0 <= out_size)) (PreH42 : (out_size <= k)) (PreH43 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH44 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 6) ” 
  &&  “ (d <> 5) ” 
  &&  “ (d <> 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_13 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 7)) (PreH2 : (d <> 6)) (PreH3 : (d <> 5)) (PreH4 : (d <> 4)) (PreH5 : (d <> 3)) (PreH6 : (d <> 2)) (PreH7 : (d <> 1)) (PreH8 : (d <= 9)) (PreH9 : (d >= 1)) (PreH10 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH11 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH12 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH13 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH14 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH15 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH16 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH17 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH18 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (tmp <> 0)) (PreH22 : (arr_pre <> 0)) (PreH23 : (0 <= arr_size_pre)) (PreH24 : (arr_size_pre < INT_MAX)) (PreH25 : (arr_size_pre = (Zlength (input_l)))) (PreH26 : (arr_size_pre = (Zlength (sorted_l)))) (PreH27 : (problem_105_pre_z input_l )) (PreH28 : (sorted_int_list_by 1 sorted_l )) (PreH29 : (Permutation input_l sorted_l )) (PreH30 : (int_range_list_105 sorted_l )) (PreH31 : (digit_payloads_string_safe_105 )) (PreH32 : (0 <= k)) (PreH33 : (k < arr_size_pre)) (PreH34 : (0 <= i)) (PreH35 : (i < arr_size_pre)) (PreH36 : (i = ((arr_size_pre - 1 ) - k ))) (PreH37 : (INT_MIN <= d)) (PreH38 : (d <= INT_MAX)) (PreH39 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH40 : (out_size = (Zlength (output_rows)))) (PreH41 : (out_size = (Zlength (output_ptrs)))) (PreH42 : (0 <= out_size)) (PreH43 : (out_size <= k)) (PreH44 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH45 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 7) ” 
  &&  “ (d <> 6) ” 
  &&  “ (d <> 5) ” 
  &&  “ (d <> 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_14 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d = 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l )) (PreH30 : (Permutation input_l sorted_l )) (PreH31 : (int_range_list_105 sorted_l )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH41 : (out_size = (Zlength (output_rows)))) (PreH42 : (out_size = (Zlength (output_ptrs)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d = 8) ” 
  &&  “ (d <> 7) ” 
  &&  “ (d <> 6) ” 
  &&  “ (d <> 5) ” 
  &&  “ (d <> 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_15 := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (k: Z) (out_size: Z) (PreH1 : (d <> 8)) (PreH2 : (d <> 7)) (PreH3 : (d <> 6)) (PreH4 : (d <> 5)) (PreH5 : (d <> 4)) (PreH6 : (d <> 3)) (PreH7 : (d <> 2)) (PreH8 : (d <> 1)) (PreH9 : (d <= 9)) (PreH10 : (d >= 1)) (PreH11 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH12 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH13 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH14 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH15 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH16 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH17 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH18 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH19 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (tmp <> 0)) (PreH23 : (arr_pre <> 0)) (PreH24 : (0 <= arr_size_pre)) (PreH25 : (arr_size_pre < INT_MAX)) (PreH26 : (arr_size_pre = (Zlength (input_l)))) (PreH27 : (arr_size_pre = (Zlength (sorted_l)))) (PreH28 : (problem_105_pre_z input_l )) (PreH29 : (sorted_int_list_by 1 sorted_l )) (PreH30 : (Permutation input_l sorted_l )) (PreH31 : (int_range_list_105 sorted_l )) (PreH32 : (digit_payloads_string_safe_105 )) (PreH33 : (0 <= k)) (PreH34 : (k < arr_size_pre)) (PreH35 : (0 <= i)) (PreH36 : (i < arr_size_pre)) (PreH37 : (i = ((arr_size_pre - 1 ) - k ))) (PreH38 : (INT_MIN <= d)) (PreH39 : (d <= INT_MAX)) (PreH40 : (output_state_105 LitMap sorted_l k output_rows output_ptrs )) (PreH41 : (out_size = (Zlength (output_rows)))) (PreH42 : (out_size = (Zlength (output_ptrs)))) (PreH43 : (0 <= out_size)) (PreH44 : (out_size <= k)) (PreH45 : (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre)))) (PreH46 : (d = (Znth (i) (sorted_l) (0)))) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (d <> 8) ” 
  &&  “ (d <> 7) ” 
  &&  “ (d <> 6) ” 
  &&  “ (d <> 5) ” 
  &&  “ (d <> 4) ” 
  &&  “ (d <> 3) ” 
  &&  “ (d <> 2) ” 
  &&  “ (d <> 1) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d >= 1) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (digit_payloads_string_safe_105 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < arr_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < arr_size_pre) ” 
  &&  “ (i = ((arr_size_pre - 1 ) - k )) ” 
  &&  “ (INT_MIN <= d) ” 
  &&  “ (d <= INT_MAX) ” 
  &&  “ (output_state_105 LitMap sorted_l k output_rows output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= k) ” 
  &&  “ (output_ptrs = (digit_ptrs_between_105 (LitMap) (sorted_l) ((arr_size_pre - k )) (arr_size_pre))) ” 
  &&  “ (d = (Znth (i) (sorted_l) (0))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data out_size (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_16_pure := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (d: Z) (i: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l )) (PreH20 : (Permutation input_l sorted_l )) (PreH21 : (int_range_list_105 sorted_l )) (PreH22 : (output_state_105 LitMap sorted_l arr_size_pre output_rows output_ptrs )) (PreH23 : (problem_105_spec_z_of_output_state input_l sorted_l output_rows LitMap output_ptrs )) (PreH24 : (out_size = (Zlength (output_rows)))) (PreH25 : (out_size = (Zlength (output_ptrs)))) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= arr_size_pre)) ,
  ((( &( "one" ) )) # Ptr  |-> one)
  **  ((( &( "two" ) )) # Ptr  |-> two)
  **  ((( &( "three" ) )) # Ptr  |-> three)
  **  ((( &( "four" ) )) # Ptr  |-> four)
  **  ((( &( "five" ) )) # Ptr  |-> five)
  **  ((( &( "six" ) )) # Ptr  |-> six)
  **  ((( &( "seven" ) )) # Ptr  |-> seven)
  **  ((( &( "eight" ) )) # Ptr  |-> eight)
  **  ((( &( "nine" ) )) # Ptr  |-> nine)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "tmp" ) )) # Ptr  |-> tmp)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (tmp <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ”
.

Definition by_length_partial_solve_wit_16_aux := 
forall (arr_size_pre: Z) (arr_pre: Z) (input_l: (@list Z)) (sorted_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (one: Z) (two: Z) (three: Z) (four: Z) (five: Z) (six: Z) (seven: Z) (eight: Z) (nine: Z) (out: Z) (data: Z) (tmp: Z) (out_size: Z) (PreH1 : (one = (digit_ptr_105 (LitMap) (1)))) (PreH2 : (two = (digit_ptr_105 (LitMap) (2)))) (PreH3 : (three = (digit_ptr_105 (LitMap) (3)))) (PreH4 : (four = (digit_ptr_105 (LitMap) (4)))) (PreH5 : (five = (digit_ptr_105 (LitMap) (5)))) (PreH6 : (six = (digit_ptr_105 (LitMap) (6)))) (PreH7 : (seven = (digit_ptr_105 (LitMap) (7)))) (PreH8 : (eight = (digit_ptr_105 (LitMap) (8)))) (PreH9 : (nine = (digit_ptr_105 (LitMap) (9)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (tmp <> 0)) (PreH13 : (arr_pre <> 0)) (PreH14 : (0 <= arr_size_pre)) (PreH15 : (arr_size_pre < INT_MAX)) (PreH16 : (arr_size_pre = (Zlength (input_l)))) (PreH17 : (arr_size_pre = (Zlength (sorted_l)))) (PreH18 : (problem_105_pre_z input_l )) (PreH19 : (sorted_int_list_by 1 sorted_l )) (PreH20 : (Permutation input_l sorted_l )) (PreH21 : (int_range_list_105 sorted_l )) (PreH22 : (output_state_105 LitMap sorted_l arr_size_pre output_rows output_ptrs )) (PreH23 : (problem_105_spec_z_of_output_state input_l sorted_l output_rows LitMap output_ptrs )) (PreH24 : (out_size = (Zlength (output_rows)))) (PreH25 : (out_size = (Zlength (output_ptrs)))) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= arr_size_pre)) ,
  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (IntArray.full tmp arr_size_pre sorted_l )
  **  (digit_literals_heap_105 LitMap )
|--
  “ (tmp <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (one = (digit_ptr_105 (LitMap) (1))) ” 
  &&  “ (two = (digit_ptr_105 (LitMap) (2))) ” 
  &&  “ (three = (digit_ptr_105 (LitMap) (3))) ” 
  &&  “ (four = (digit_ptr_105 (LitMap) (4))) ” 
  &&  “ (five = (digit_ptr_105 (LitMap) (5))) ” 
  &&  “ (six = (digit_ptr_105 (LitMap) (6))) ” 
  &&  “ (seven = (digit_ptr_105 (LitMap) (7))) ” 
  &&  “ (eight = (digit_ptr_105 (LitMap) (8))) ” 
  &&  “ (nine = (digit_ptr_105 (LitMap) (9))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (tmp <> 0) ” 
  &&  “ (arr_pre <> 0) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (input_l))) ” 
  &&  “ (arr_size_pre = (Zlength (sorted_l))) ” 
  &&  “ (problem_105_pre_z input_l ) ” 
  &&  “ (sorted_int_list_by 1 sorted_l ) ” 
  &&  “ (Permutation input_l sorted_l ) ” 
  &&  “ (int_range_list_105 sorted_l ) ” 
  &&  “ (output_state_105 LitMap sorted_l arr_size_pre output_rows output_ptrs ) ” 
  &&  “ (problem_105_spec_z_of_output_state input_l sorted_l output_rows LitMap output_ptrs ) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out_size = (Zlength (output_ptrs))) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= arr_size_pre) ”
  &&  (IntArray.full tmp arr_size_pre sorted_l )
  **  (IntArray.full arr_pre arr_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 (Zlength (output_ptrs)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_ptrs)) arr_size_pre )
  **  (digit_literals_heap_105 LitMap )
.

Definition by_length_partial_solve_wit_16 := by_length_partial_solve_wit_16_pure -> by_length_partial_solve_wit_16_aux.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_by_length_safety_wit_1 : by_length_safety_wit_1.
Axiom proof_of_by_length_safety_wit_2 : by_length_safety_wit_2.
Axiom proof_of_by_length_safety_wit_3 : by_length_safety_wit_3.
Axiom proof_of_by_length_safety_wit_4 : by_length_safety_wit_4.
Axiom proof_of_by_length_safety_wit_5 : by_length_safety_wit_5.
Axiom proof_of_by_length_safety_wit_6 : by_length_safety_wit_6.
Axiom proof_of_by_length_safety_wit_7 : by_length_safety_wit_7.
Axiom proof_of_by_length_safety_wit_8 : by_length_safety_wit_8.
Axiom proof_of_by_length_safety_wit_9 : by_length_safety_wit_9.
Axiom proof_of_by_length_safety_wit_10 : by_length_safety_wit_10.
Axiom proof_of_by_length_safety_wit_11 : by_length_safety_wit_11.
Axiom proof_of_by_length_safety_wit_12 : by_length_safety_wit_12.
Axiom proof_of_by_length_safety_wit_13 : by_length_safety_wit_13.
Axiom proof_of_by_length_safety_wit_14 : by_length_safety_wit_14.
Axiom proof_of_by_length_safety_wit_15 : by_length_safety_wit_15.
Axiom proof_of_by_length_safety_wit_16 : by_length_safety_wit_16.
Axiom proof_of_by_length_safety_wit_17 : by_length_safety_wit_17.
Axiom proof_of_by_length_safety_wit_18 : by_length_safety_wit_18.
Axiom proof_of_by_length_safety_wit_19 : by_length_safety_wit_19.
Axiom proof_of_by_length_safety_wit_20 : by_length_safety_wit_20.
Axiom proof_of_by_length_safety_wit_21 : by_length_safety_wit_21.
Axiom proof_of_by_length_safety_wit_22 : by_length_safety_wit_22.
Axiom proof_of_by_length_safety_wit_23 : by_length_safety_wit_23.
Axiom proof_of_by_length_safety_wit_24 : by_length_safety_wit_24.
Axiom proof_of_by_length_safety_wit_25 : by_length_safety_wit_25.
Axiom proof_of_by_length_safety_wit_26 : by_length_safety_wit_26.
Axiom proof_of_by_length_safety_wit_27 : by_length_safety_wit_27.
Axiom proof_of_by_length_safety_wit_28 : by_length_safety_wit_28.
Axiom proof_of_by_length_safety_wit_29 : by_length_safety_wit_29.
Axiom proof_of_by_length_safety_wit_30 : by_length_safety_wit_30.
Axiom proof_of_by_length_safety_wit_31 : by_length_safety_wit_31.
Axiom proof_of_by_length_safety_wit_32 : by_length_safety_wit_32.
Axiom proof_of_by_length_safety_wit_33 : by_length_safety_wit_33.
Axiom proof_of_by_length_safety_wit_34 : by_length_safety_wit_34.
Axiom proof_of_by_length_safety_wit_35 : by_length_safety_wit_35.
Axiom proof_of_by_length_safety_wit_36 : by_length_safety_wit_36.
Axiom proof_of_by_length_safety_wit_37 : by_length_safety_wit_37.
Axiom proof_of_by_length_safety_wit_38 : by_length_safety_wit_38.
Axiom proof_of_by_length_safety_wit_39 : by_length_safety_wit_39.
Axiom proof_of_by_length_entail_wit_1 : by_length_entail_wit_1.
Axiom proof_of_by_length_entail_wit_2 : by_length_entail_wit_2.
Axiom proof_of_by_length_entail_wit_3 : by_length_entail_wit_3.
Axiom proof_of_by_length_entail_wit_4 : by_length_entail_wit_4.
Axiom proof_of_by_length_entail_wit_5 : by_length_entail_wit_5.
Axiom proof_of_by_length_entail_wit_6 : by_length_entail_wit_6.
Axiom proof_of_by_length_entail_wit_7 : by_length_entail_wit_7.
Axiom proof_of_by_length_entail_wit_8 : by_length_entail_wit_8.
Axiom proof_of_by_length_entail_wit_9_1 : by_length_entail_wit_9_1.
Axiom proof_of_by_length_entail_wit_9_2 : by_length_entail_wit_9_2.
Axiom proof_of_by_length_entail_wit_9_3 : by_length_entail_wit_9_3.
Axiom proof_of_by_length_entail_wit_9_4 : by_length_entail_wit_9_4.
Axiom proof_of_by_length_entail_wit_9_5 : by_length_entail_wit_9_5.
Axiom proof_of_by_length_entail_wit_9_6 : by_length_entail_wit_9_6.
Axiom proof_of_by_length_entail_wit_9_7 : by_length_entail_wit_9_7.
Axiom proof_of_by_length_entail_wit_9_8 : by_length_entail_wit_9_8.
Axiom proof_of_by_length_entail_wit_9_9 : by_length_entail_wit_9_9.
Axiom proof_of_by_length_entail_wit_9_10 : by_length_entail_wit_9_10.
Axiom proof_of_by_length_entail_wit_9_11 : by_length_entail_wit_9_11.
Axiom proof_of_by_length_entail_wit_10 : by_length_entail_wit_10.
Axiom proof_of_by_length_entail_wit_11 : by_length_entail_wit_11.
Axiom proof_of_by_length_entail_wit_12 : by_length_entail_wit_12.
Axiom proof_of_by_length_return_wit_1 : by_length_return_wit_1.
Axiom proof_of_by_length_partial_solve_wit_1 : by_length_partial_solve_wit_1.
Axiom proof_of_by_length_partial_solve_wit_2_pure : by_length_partial_solve_wit_2_pure.
Axiom proof_of_by_length_partial_solve_wit_2 : by_length_partial_solve_wit_2.
Axiom proof_of_by_length_partial_solve_wit_3_pure : by_length_partial_solve_wit_3_pure.
Axiom proof_of_by_length_partial_solve_wit_3 : by_length_partial_solve_wit_3.
Axiom proof_of_by_length_partial_solve_wit_4 : by_length_partial_solve_wit_4.
Axiom proof_of_by_length_partial_solve_wit_5 : by_length_partial_solve_wit_5.
Axiom proof_of_by_length_partial_solve_wit_6_pure : by_length_partial_solve_wit_6_pure.
Axiom proof_of_by_length_partial_solve_wit_6 : by_length_partial_solve_wit_6.
Axiom proof_of_by_length_partial_solve_wit_7 : by_length_partial_solve_wit_7.
Axiom proof_of_by_length_partial_solve_wit_8 : by_length_partial_solve_wit_8.
Axiom proof_of_by_length_partial_solve_wit_9 : by_length_partial_solve_wit_9.
Axiom proof_of_by_length_partial_solve_wit_10 : by_length_partial_solve_wit_10.
Axiom proof_of_by_length_partial_solve_wit_11 : by_length_partial_solve_wit_11.
Axiom proof_of_by_length_partial_solve_wit_12 : by_length_partial_solve_wit_12.
Axiom proof_of_by_length_partial_solve_wit_13 : by_length_partial_solve_wit_13.
Axiom proof_of_by_length_partial_solve_wit_14 : by_length_partial_solve_wit_14.
Axiom proof_of_by_length_partial_solve_wit_15 : by_length_partial_solve_wit_15.
Axiom proof_of_by_length_partial_solve_wit_16_pure : by_length_partial_solve_wit_16_pure.
Axiom proof_of_by_length_partial_solve_wit_16 : by_length_partial_solve_wit_16.

End VC_Correct.
