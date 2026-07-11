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
Require Import p101_words_string.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function words_string -----*)

Definition words_string_safety_wit_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_words_input_101 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_101_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_string_safety_wit_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_words_input_101 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_101_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_words_input_101 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_101_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_4 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_words_input_101 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_101_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_5 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_words_input_101 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_101_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition words_string_safety_wit_6 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_words_input_101 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_101_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_7 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_8 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_9 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_10 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_11 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition words_string_safety_wit_12 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (44 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 44) ”
.

Definition words_string_safety_wit_13 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_14 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_15 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_string_safety_wit_16 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition words_string_safety_wit_17 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition words_string_safety_wit_18 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_19 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition words_string_safety_wit_20 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_21 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_22 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_23 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_delim_z_101 (ch)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows )) (PreH27 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH28 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition words_string_safety_wit_24 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows )) (PreH28 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH29 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition words_string_safety_wit_25 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_delim_z_101 (ch)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows )) (PreH27 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH28 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_26 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) (PreH26 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition words_string_safety_wit_27 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) (PreH26 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_string_safety_wit_28 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) (PreH26 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_29 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 44)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_30 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : ((is_delim_z_101 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l (i + 1 ) start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_31 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : ((is_delim_z_101 (ch)) = true)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_words_input_101 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_101_pre_z str_l )) (PreH21 : (split_scan_state_101 str_l (i + 1 ) start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_32 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_words_input_101 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_101_pre_z str_l )) (PreH21 : (split_scan_state_101 str_l (i + 1 ) start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition words_string_safety_wit_33 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_34 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((n - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - start )) ”
.

Definition words_string_safety_wit_35 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - start ) + 1 )) ”
.

Definition words_string_safety_wit_36 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_safety_wit_37 := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_38 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l n start output_rows )) (PreH23 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH24 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition words_string_safety_wit_39 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l n start output_rows )) (PreH24 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH25 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition words_string_safety_wit_40 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l n start output_rows )) (PreH23 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH24 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition words_string_safety_wit_41 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition words_string_safety_wit_42 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition words_string_safety_wit_43 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition words_string_entail_wit_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = 0) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l 0 (-1) output_rows ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg retval_3 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_3 0 (retval + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_words_input_101 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_101_pre_z str_l )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l 0 (-1) output_rows ) ”
  &&  (words_rows_heap_101 (@nil Z) output_rows )
).

Definition words_string_entail_wit_2_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_101 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((word_payload_101 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = (i - start )) ”
  &&  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_2_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((i - start ) = (i - start )) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_101 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((word_payload_101 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = (i - start )) ”
  &&  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_3 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH28 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH29 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_101 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
) \/
(
forall (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH28 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH29 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) = (word_payload_101 (str_l) (start) ((start + (k + 1 ) )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_4 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_words_input_101 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_101_pre_z str_l )) (PreH27 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH28 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH29 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
) \/
(
forall (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((is_delim_z_101 (ch)) = true)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_words_input_101 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_101_pre_z str_l )) (PreH28 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH29 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH30 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
).

Definition words_string_entail_wit_5 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH26 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = (out_size + 1 )) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) (-1) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_delim_z_101 (ch)) = true)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) (PreH26 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z))))))) = (out_size + 1 )) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) (-1) output_rows ) ”
  &&  (words_rows_heap_101 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) output_rows )
).

Definition words_string_entail_wit_6_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_6_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ ((is_delim_z_101 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_7_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 44)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_7_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) i output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 44)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) i output_rows ) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_8_1 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : ((is_delim_z_101 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l (i + 1 ) start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_entail_wit_8_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : ((is_delim_z_101 (ch)) = true)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_words_input_101 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_101_pre_z str_l )) (PreH21 : (split_scan_state_101 str_l (i + 1 ) start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_entail_wit_8_3 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= len)) (PreH15 : (len < INT_MAX)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_words_input_101 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_101_pre_z str_l )) (PreH21 : (split_scan_state_101 str_l (i + 1 ) start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l (i + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_entail_wit_9 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ ((n - start ) = (n - start )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_101 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((word_payload_101 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n - start )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = (n - start )) ”
  &&  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_10 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH24 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH25 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_101 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
) \/
(
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH24 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH25 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) = (word_payload_101 (str_l) (start) ((start + (k + 1 ) )))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len) ”
  &&  (words_rows_heap_101 output_ptrs_2 output_rows )
).

Definition words_string_entail_wit_11_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (output_rows = (words_output_rows_101 (str_l))) ” 
  &&  “ (problem_101_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ (problem_101_spec_z str_l (words_output_rows_101 (str_l)) ) ” 
  &&  “ (out_size = (Zlength ((words_output_rows_101 (str_l))))) ”
  &&  (words_rows_heap_101 output_ptrs_2 (words_output_rows_101 (str_l)) )
).

Definition words_string_entail_wit_11_1_split_goal_1 := 
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ (problem_101_spec_z str_l (words_output_rows_101 (str_l)) ) ”
.

Definition words_string_entail_wit_11_1_split_goal_2 := 
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ (out_size = (Zlength ((words_output_rows_101 (str_l))))) ”
.

Definition words_string_entail_wit_11_1_split_goal_spatial := 
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows_2 )) ,
  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  (words_rows_heap_101 output_ptrs_2 (words_output_rows_101 (str_l)) )
.

Definition words_string_entail_wit_11_2 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = (out_size + 1 )) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (output_rows = (words_output_rows_101 (str_l))) ” 
  &&  “ (problem_101_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ (problem_101_spec_z str_l (words_output_rows_101 (str_l)) ) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z))))))) = (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((words_output_rows_101 (str_l))))) ”
  &&  (words_rows_heap_101 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) (words_output_rows_101 (str_l)) )
).

Definition words_string_entail_wit_11_2_split_goal_1 := 
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ (problem_101_spec_z str_l (words_output_rows_101 (str_l)) ) ”
.

Definition words_string_entail_wit_11_2_split_goal_2 := 
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ ((Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z))))))) = (out_size + 1 )) ”
.

Definition words_string_entail_wit_11_2_split_goal_3 := 
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  “ ((out_size + 1 ) = (Zlength ((words_output_rows_101 (str_l))))) ”
.

Definition words_string_entail_wit_11_2_split_goal_spatial := 
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (0 <= k)) (PreH18 : (k <= len)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l n start output_rows_2 )) (PreH25 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH26 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  (words_rows_heap_101 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) (words_output_rows_101 (str_l)) )
.

Definition words_string_return_wit_1 := 
(
forall (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (valid_string str_l )) (PreH12 : (all_ascii str_l )) (PreH13 : (valid_words_input_101 str_l )) (PreH14 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH15 : (problem_101_pre_z str_l )) (PreH16 : (output_rows_2 = (words_output_rows_101 (str_l)))) (PreH17 : (problem_101_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (problem_101_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (out_size: Z) (start: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (valid_string str_l )) (PreH13 : (all_ascii str_l )) (PreH14 : (valid_words_input_101 str_l )) (PreH15 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH16 : (problem_101_pre_z str_l )) (PreH17 : (output_rows_2 = (words_output_rows_101 (str_l)))) (PreH18 : (problem_101_spec_z str_l output_rows_2 )) ,
  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (problem_101_spec_z str_l output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
).

Definition words_string_partial_solve_wit_1_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_words_input_101 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_101_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_1_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_words_input_101 str_l )) (PreH4 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH5 : (problem_101_pre_z str_l )) ,
  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ”
  &&  (store_string s_pre str_l )
.

Definition words_string_partial_solve_wit_1 := words_string_partial_solve_wit_1_pure -> words_string_partial_solve_wit_1_aux.

Definition words_string_partial_solve_wit_2 := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_words_input_101 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_101_pre_z str_l )) ,
  (store_string s_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition words_string_partial_solve_wit_3_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_words_input_101 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_101_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_3_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_words_input_101 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_101_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition words_string_partial_solve_wit_3 := words_string_partial_solve_wit_3_pure -> words_string_partial_solve_wit_3_aux.

Definition words_string_partial_solve_wit_4_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_4_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_words_input_101 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_101_pre_z str_l )) (PreH24 : (split_scan_state_101 str_l i start output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_partial_solve_wit_4 := words_string_partial_solve_wit_4_pure -> words_string_partial_solve_wit_4_aux.

Definition words_string_partial_solve_wit_5_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_5_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 44)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_words_input_101 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_101_pre_z str_l )) (PreH25 : (split_scan_state_101 str_l i start output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 44) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 32) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_partial_solve_wit_5 := words_string_partial_solve_wit_5_pure -> words_string_partial_solve_wit_5_aux.

Definition words_string_partial_solve_wit_6 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_delim_z_101 (ch)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows )) (PreH27 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH28 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
.

Definition words_string_partial_solve_wit_7 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_delim_z_101 (ch)) = true)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_words_input_101 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_101_pre_z str_l )) (PreH26 : (split_scan_state_101 str_l i start output_rows )) (PreH27 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) (PreH28 : ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k >= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (i)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
.

Definition words_string_partial_solve_wit_8 := 
forall (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (0 <= start)) (PreH12 : (start < i)) (PreH13 : (len = (i - start ))) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : ((is_delim_z_101 (ch)) = true)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) (PreH24 : ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (len = (i - start )) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((is_delim_z_101 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (i)) = (word_payload_101 (str_l) (start) (i))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_101 (str_l) (start) (i)) )
.

Definition words_string_partial_solve_wit_9_pure := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) > 0) ” 
  &&  “ (((n - start ) + 1 ) < INT_MAX) ”
.

Definition words_string_partial_solve_wit_9_aux := 
forall (s_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l i start output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) > 0) ” 
  &&  “ (((n - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (start >= 0) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l i start output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Definition words_string_partial_solve_wit_9 := words_string_partial_solve_wit_9_pure -> words_string_partial_solve_wit_9_aux.

Definition words_string_partial_solve_wit_10 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l n start output_rows )) (PreH23 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH24 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k < len) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
.

Definition words_string_partial_solve_wit_11 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= n)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < n)) (PreH14 : (len = (n - start ))) (PreH15 : (0 <= k)) (PreH16 : (k <= len)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_words_input_101 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_101_pre_z str_l )) (PreH22 : (split_scan_state_101 str_l n start output_rows )) (PreH23 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH24 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k >= len) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_101 (str_l) (start) ((start + k ))) )
.

Definition words_string_partial_solve_wit_12 := 
forall (s_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= n)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < n)) (PreH15 : (len = (n - start ))) (PreH16 : (0 <= k)) (PreH17 : (k <= len)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_words_input_101 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_101_pre_z str_l )) (PreH23 : (split_scan_state_101 str_l n start output_rows )) (PreH24 : ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n)))) (PreH25 : ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (words_rows_heap_101 output_ptrs output_rows )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k >= len) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_words_input_101 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_101_pre_z str_l ) ” 
  &&  “ (split_scan_state_101 str_l n start output_rows ) ” 
  &&  “ ((split_scan_current_101 (str_l) (n)) = (word_payload_101 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_101 (str_l) (start) (n)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_101 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (words_rows_heap_101 output_ptrs output_rows )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_words_string_safety_wit_1 : words_string_safety_wit_1.
Axiom proof_of_words_string_safety_wit_2 : words_string_safety_wit_2.
Axiom proof_of_words_string_safety_wit_3 : words_string_safety_wit_3.
Axiom proof_of_words_string_safety_wit_4 : words_string_safety_wit_4.
Axiom proof_of_words_string_safety_wit_5 : words_string_safety_wit_5.
Axiom proof_of_words_string_safety_wit_6 : words_string_safety_wit_6.
Axiom proof_of_words_string_safety_wit_7 : words_string_safety_wit_7.
Axiom proof_of_words_string_safety_wit_8 : words_string_safety_wit_8.
Axiom proof_of_words_string_safety_wit_9 : words_string_safety_wit_9.
Axiom proof_of_words_string_safety_wit_10 : words_string_safety_wit_10.
Axiom proof_of_words_string_safety_wit_11 : words_string_safety_wit_11.
Axiom proof_of_words_string_safety_wit_12 : words_string_safety_wit_12.
Axiom proof_of_words_string_safety_wit_13 : words_string_safety_wit_13.
Axiom proof_of_words_string_safety_wit_14 : words_string_safety_wit_14.
Axiom proof_of_words_string_safety_wit_15 : words_string_safety_wit_15.
Axiom proof_of_words_string_safety_wit_16 : words_string_safety_wit_16.
Axiom proof_of_words_string_safety_wit_17 : words_string_safety_wit_17.
Axiom proof_of_words_string_safety_wit_18 : words_string_safety_wit_18.
Axiom proof_of_words_string_safety_wit_19 : words_string_safety_wit_19.
Axiom proof_of_words_string_safety_wit_20 : words_string_safety_wit_20.
Axiom proof_of_words_string_safety_wit_21 : words_string_safety_wit_21.
Axiom proof_of_words_string_safety_wit_22 : words_string_safety_wit_22.
Axiom proof_of_words_string_safety_wit_23 : words_string_safety_wit_23.
Axiom proof_of_words_string_safety_wit_24 : words_string_safety_wit_24.
Axiom proof_of_words_string_safety_wit_25 : words_string_safety_wit_25.
Axiom proof_of_words_string_safety_wit_26 : words_string_safety_wit_26.
Axiom proof_of_words_string_safety_wit_27 : words_string_safety_wit_27.
Axiom proof_of_words_string_safety_wit_28 : words_string_safety_wit_28.
Axiom proof_of_words_string_safety_wit_29 : words_string_safety_wit_29.
Axiom proof_of_words_string_safety_wit_30 : words_string_safety_wit_30.
Axiom proof_of_words_string_safety_wit_31 : words_string_safety_wit_31.
Axiom proof_of_words_string_safety_wit_32 : words_string_safety_wit_32.
Axiom proof_of_words_string_safety_wit_33 : words_string_safety_wit_33.
Axiom proof_of_words_string_safety_wit_34 : words_string_safety_wit_34.
Axiom proof_of_words_string_safety_wit_35 : words_string_safety_wit_35.
Axiom proof_of_words_string_safety_wit_36 : words_string_safety_wit_36.
Axiom proof_of_words_string_safety_wit_37 : words_string_safety_wit_37.
Axiom proof_of_words_string_safety_wit_38 : words_string_safety_wit_38.
Axiom proof_of_words_string_safety_wit_39 : words_string_safety_wit_39.
Axiom proof_of_words_string_safety_wit_40 : words_string_safety_wit_40.
Axiom proof_of_words_string_safety_wit_41 : words_string_safety_wit_41.
Axiom proof_of_words_string_safety_wit_42 : words_string_safety_wit_42.
Axiom proof_of_words_string_safety_wit_43 : words_string_safety_wit_43.
Axiom proof_of_words_string_entail_wit_1 : words_string_entail_wit_1.
Axiom proof_of_words_string_entail_wit_2_1 : words_string_entail_wit_2_1.
Axiom proof_of_words_string_entail_wit_2_2 : words_string_entail_wit_2_2.
Axiom proof_of_words_string_entail_wit_3 : words_string_entail_wit_3.
Axiom proof_of_words_string_entail_wit_4 : words_string_entail_wit_4.
Axiom proof_of_words_string_entail_wit_5 : words_string_entail_wit_5.
Axiom proof_of_words_string_entail_wit_6_1 : words_string_entail_wit_6_1.
Axiom proof_of_words_string_entail_wit_6_2 : words_string_entail_wit_6_2.
Axiom proof_of_words_string_entail_wit_7_1 : words_string_entail_wit_7_1.
Axiom proof_of_words_string_entail_wit_7_2 : words_string_entail_wit_7_2.
Axiom proof_of_words_string_entail_wit_8_1 : words_string_entail_wit_8_1.
Axiom proof_of_words_string_entail_wit_8_2 : words_string_entail_wit_8_2.
Axiom proof_of_words_string_entail_wit_8_3 : words_string_entail_wit_8_3.
Axiom proof_of_words_string_entail_wit_9 : words_string_entail_wit_9.
Axiom proof_of_words_string_entail_wit_10 : words_string_entail_wit_10.
Axiom proof_of_words_string_entail_wit_11_1 : words_string_entail_wit_11_1.
Axiom proof_of_words_string_entail_wit_11_2 : words_string_entail_wit_11_2.
Axiom proof_of_words_string_return_wit_1 : words_string_return_wit_1.
Axiom proof_of_words_string_partial_solve_wit_1_pure : words_string_partial_solve_wit_1_pure.
Axiom proof_of_words_string_partial_solve_wit_1 : words_string_partial_solve_wit_1.
Axiom proof_of_words_string_partial_solve_wit_2 : words_string_partial_solve_wit_2.
Axiom proof_of_words_string_partial_solve_wit_3_pure : words_string_partial_solve_wit_3_pure.
Axiom proof_of_words_string_partial_solve_wit_3 : words_string_partial_solve_wit_3.
Axiom proof_of_words_string_partial_solve_wit_4_pure : words_string_partial_solve_wit_4_pure.
Axiom proof_of_words_string_partial_solve_wit_4 : words_string_partial_solve_wit_4.
Axiom proof_of_words_string_partial_solve_wit_5_pure : words_string_partial_solve_wit_5_pure.
Axiom proof_of_words_string_partial_solve_wit_5 : words_string_partial_solve_wit_5.
Axiom proof_of_words_string_partial_solve_wit_6 : words_string_partial_solve_wit_6.
Axiom proof_of_words_string_partial_solve_wit_7 : words_string_partial_solve_wit_7.
Axiom proof_of_words_string_partial_solve_wit_8 : words_string_partial_solve_wit_8.
Axiom proof_of_words_string_partial_solve_wit_9_pure : words_string_partial_solve_wit_9_pure.
Axiom proof_of_words_string_partial_solve_wit_9 : words_string_partial_solve_wit_9.
Axiom proof_of_words_string_partial_solve_wit_10 : words_string_partial_solve_wit_10.
Axiom proof_of_words_string_partial_solve_wit_11 : words_string_partial_solve_wit_11.
Axiom proof_of_words_string_partial_solve_wit_12 : words_string_partial_solve_wit_12.

End VC_Correct.
