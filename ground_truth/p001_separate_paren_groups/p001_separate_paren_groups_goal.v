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
Require Import p001_separate_paren_groups.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function separate_paren_groups -----*)

Definition separate_paren_groups_safety_wit_1 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_input_1 str_l )) (PreH7 : (paren_safe_input_1 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_1_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_2 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_input_1 str_l )) (PreH7 : (paren_safe_input_1 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_1_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition separate_paren_groups_safety_wit_3 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_input_1 str_l )) (PreH7 : (paren_safe_input_1 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_1_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_4 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_5 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "level" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_6 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition separate_paren_groups_safety_wit_7 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_8 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_9 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_10 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_11 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (40 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 40) ”
.

Definition separate_paren_groups_safety_wit_12 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_13 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition separate_paren_groups_safety_wit_14 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_15 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition separate_paren_groups_safety_wit_16 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_17 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (41 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 41) ”
.

Definition separate_paren_groups_safety_wit_18 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((level - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level - 1 )) ”
.

Definition separate_paren_groups_safety_wit_19 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_20 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_21 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition separate_paren_groups_safety_wit_22 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition separate_paren_groups_safety_wit_23 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_24 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "row" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> ((i - start ) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((((i - start ) + 1 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((i - start ) + 1 ) + 1 )) ”
.

Definition separate_paren_groups_safety_wit_25 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "row" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> ((i - start ) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_26 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((level - 1 ) = 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : (0 <= level)) (PreH17 : (level <= i)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_paren_input_1 str_l )) (PreH27 : (paren_safe_input_1 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_1_pre_z str_l )) (PreH30 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval (((i - start ) + 1 ) + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "row" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> ((i - start ) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_27 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (row <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (ch = 41)) (PreH13 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH14 : (level = 0)) (PreH15 : (0 <= start)) (PreH16 : (start <= i)) (PreH17 : (len = ((i - start ) + 1 ))) (PreH18 : (0 <= k)) (PreH19 : (k <= len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i 1 start output_rows )) (PreH27 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg row k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition separate_paren_groups_safety_wit_28 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i 1 start output_rows )) (PreH28 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  (CharArray.full row (k + 1 ) (app ((paren_payload_1 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg row (k + 1 ) (len + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition separate_paren_groups_safety_wit_29 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (row <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (ch = 41)) (PreH13 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH14 : (level = 0)) (PreH15 : (0 <= start)) (PreH16 : (start <= i)) (PreH17 : (len = ((i - start ) + 1 ))) (PreH18 : (0 <= k)) (PreH19 : (k <= len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i 1 start output_rows )) (PreH27 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg row k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition separate_paren_groups_safety_wit_30 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i 1 start output_rows )) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (row) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition separate_paren_groups_safety_wit_31 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i 1 start output_rows )) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (row) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition separate_paren_groups_safety_wit_32 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i 1 start output_rows )) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (row) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "row" ) )) # Ptr  |-> row)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition separate_paren_groups_safety_wit_33 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (ch = 40)) (PreH11 : (0 <= level)) (PreH12 : (level <= (i + 1 ))) (PreH13 : (0 <= start)) (PreH14 : (start <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition separate_paren_groups_safety_wit_34 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (row <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (ch = 41)) (PreH12 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH13 : (level = 0)) (PreH14 : (start = (-1))) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_paren_input_1 str_l )) (PreH20 : (paren_safe_input_1 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_1_pre_z str_l )) (PreH23 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition separate_paren_groups_safety_wit_35 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (ch = 41)) (PreH11 : (0 < level)) (PreH12 : (level <= i)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition separate_paren_groups_safety_wit_36 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (ch = 32)) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition separate_paren_groups_entail_wit_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l 0 0 (-1) output_rows ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg retval_3 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg retval_3 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_paren_input_1 str_l )) (PreH8 : (paren_safe_input_1 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_1_pre_z str_l )) ,
  (PtrArray.undef_full retval_3 (retval + 1 ) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) < 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l 0 0 (-1) output_rows ) ”
  &&  (PtrArray.seg retval_3 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg retval_3 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_2_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level + 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ ((Zlength (output_rows_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level + 1 ) start output_rows ) ”
  &&  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_2_2 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (level = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level + 1 ) i output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (level = 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ ((Zlength (output_rows_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 40) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level + 1 ) i output_rows ) ”
  &&  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_3 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((level - 1 ) = 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= level)) (PreH17 : (level <= i)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_paren_input_1 str_l )) (PreH27 : (paren_safe_input_1 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_1_pre_z str_l )) (PreH30 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (CharArray.undef_full retval (((i - start ) + 1 ) + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((level - 1 ) = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (((i - start ) + 1 ) = ((i - start ) + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((i - start ) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = ((i - start ) + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full retval 0 (paren_payload_1 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 (((i - start ) + 1 ) + 1 ) )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : ((level - 1 ) = 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH5 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= level)) (PreH17 : (level <= i)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_paren_input_1 str_l )) (PreH27 : (paren_safe_input_1 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_1_pre_z str_l )) (PreH30 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (CharArray.undef_full retval (((i - start ) + 1 ) + 1 ) )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ ((paren_payload_1 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
  &&  “ ((Zlength (output_rows_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ ((level - 1 ) = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((i - start ) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = ((i - start ) + 1 )) ”
  &&  (CharArray.undef_full retval (((i - start ) + 1 ) + 1 ) )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_4 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) (PreH28 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  (CharArray.full row (k + 1 ) (app ((paren_payload_1 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg row (k + 1 ) (len + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (k + 1 ) (paren_payload_1 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg row (k + 1 ) (len + 1 ) )
) \/
(
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) (PreH28 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((app ((paren_payload_1 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) = (paren_payload_1 (str_l) (start) ((start + (k + 1 ) )))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len) ”
  &&  (paren_rows_heap_1 output_ptrs_2 output_rows )
).

Definition separate_paren_groups_entail_wit_5 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) (PreH28 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  (CharArray.full row (k + 1 ) (app ((paren_payload_1 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row (len + 1 ) (len + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
) \/
(
forall (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (row <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (ch = 41)) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : (level = 0)) (PreH17 : (0 <= start)) (PreH18 : (start <= i)) (PreH19 : (len = ((i - start ) + 1 ))) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) (PreH29 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  (CharArray.full row (k + 1 ) (app ((paren_payload_1 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ”
  &&  (paren_rows_heap_1 output_ptrs_2 output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
).

Definition separate_paren_groups_entail_wit_6 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (row) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = (out_size + 1 )) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level (-1) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (row <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (ch = 41)) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : (level = 0)) (PreH16 : (0 <= start)) (PreH17 : (start <= i)) (PreH18 : (len = ((i - start ) + 1 ))) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i 1 start output_rows_2 )) ,
  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (row) ((@nil Z))))))) = (out_size + 1 )) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level (-1) output_rows ) ”
  &&  (paren_rows_heap_1 (app (output_ptrs_2) ((cons (row) ((@nil Z))))) output_rows )
).

Definition separate_paren_groups_entail_wit_7 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) <> 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (0 < (level - 1 )) ” 
  &&  “ ((level - 1 ) <= i) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level - 1 ) start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((level - 1 ) <> 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH4 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : (0 <= level)) (PreH16 : (level <= i)) (PreH17 : ((-1) <= start)) (PreH18 : (start < i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_paren_input_1 str_l )) (PreH26 : (paren_safe_input_1 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_1_pre_z str_l )) (PreH29 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ ((Zlength (output_rows_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ (0 < (level - 1 )) ” 
  &&  “ ((level - 1 ) <= i) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) (level - 1 ) start output_rows ) ”
  &&  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_8 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= level)) (PreH14 : (level <= i)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_paren_input_1 str_l )) (PreH24 : (paren_safe_input_1 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_1_pre_z str_l )) (PreH27 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ ((Zlength (output_rows_2)) = out_size) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 32) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_9_1 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (ch = 40)) (PreH11 : (0 <= level)) (PreH12 : (level <= (i + 1 ))) (PreH13 : (0 <= start)) (PreH14 : (start <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (ch = 40)) (PreH12 : (0 <= level)) (PreH13 : (level <= (i + 1 ))) (PreH14 : (0 <= start)) (PreH15 : (start <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_9_2 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (row <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (ch = 41)) (PreH12 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH13 : (level = 0)) (PreH14 : (start = (-1))) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_paren_input_1 str_l )) (PreH20 : (paren_safe_input_1 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_1_pre_z str_l )) (PreH23 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (row <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= (i + 1 ))) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : (ch = 41)) (PreH13 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH14 : (level = 0)) (PreH15 : (start = (-1))) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_input_1 str_l )) (PreH21 : (paren_safe_input_1 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_1_pre_z str_l )) (PreH24 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_9_3 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (ch = 41)) (PreH11 : (0 < level)) (PreH12 : (level <= i)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (ch = 41)) (PreH12 : (0 < level)) (PreH13 : (level <= i)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_9_4 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (ch = 32)) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (ch = 32)) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l (i + 1 ) level start output_rows_2 )) ,
  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (i + 1 )) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l (i + 1 ) level start output_rows ) ”
  &&  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
).

Definition separate_paren_groups_entail_wit_10 := 
(
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (0 <= level)) (PreH12 : (level <= i)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (valid_string str_l )) (PreH20 : (all_ascii str_l )) (PreH21 : (valid_paren_input_1 str_l )) (PreH22 : (paren_safe_input_1 str_l )) (PreH23 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH24 : (problem_1_pre_z str_l )) (PreH25 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (n + 1 )) ” 
  &&  “ (out_size < INT_MAX) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_rows)) < INT_MAX) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (level = 0) ” 
  &&  “ (start = (-1)) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (output_rows = (paren_output_rows_1 (str_l))) ” 
  &&  “ (problem_1_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
) \/
(
forall (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : (0 <= level)) (PreH13 : (level <= i)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i level start output_rows_2 )) ,
  (PtrArray.seg data 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z)) ,
  “ ((Zlength (output_rows_2)) = (Zlength ((paren_output_rows_1 (str_l))))) ” 
  &&  “ ((Zlength (output_rows_2)) = (Zlength ((paren_output_rows_1 (str_l))))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= (n + 1 )) ” 
  &&  “ (out_size < INT_MAX) ” 
  &&  “ (out_size = (Zlength ((paren_output_rows_1 (str_l))))) ” 
  &&  “ ((Zlength ((paren_output_rows_1 (str_l)))) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength ((paren_output_rows_1 (str_l)))) < INT_MAX) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength ((paren_output_rows_1 (str_l))))) ” 
  &&  “ (level = 0) ” 
  &&  “ (start = (-1)) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (problem_1_spec_z str_l (paren_output_rows_1 (str_l)) ) ”
  &&  (PtrArray.seg data 0 (Zlength ((paren_output_rows_1 (str_l)))) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength ((paren_output_rows_1 (str_l)))) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs (paren_output_rows_1 (str_l)) )
).

Definition separate_paren_groups_return_wit_1 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (out_size: Z) (level: Z) (start: Z) (ch: Z) (len: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= out_size)) (PreH5 : (out_size <= (n + 1 ))) (PreH6 : (out_size < INT_MAX)) (PreH7 : (out_size = (Zlength (output_rows_2)))) (PreH8 : ((Zlength (output_rows_2)) <= ((string_length (str_l)) + 1 ))) (PreH9 : ((Zlength (output_rows_2)) < INT_MAX)) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : ((Zlength (output_ptrs_2)) = (Zlength (output_rows_2)))) (PreH12 : (level = 0)) (PreH13 : (start = (-1))) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (valid_string str_l )) (PreH19 : (all_ascii str_l )) (PreH20 : (valid_paren_input_1 str_l )) (PreH21 : (paren_safe_input_1 str_l )) (PreH22 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH23 : (problem_1_pre_z str_l )) (PreH24 : (output_rows_2 = (paren_output_rows_1 (str_l)))) (PreH25 : (problem_1_spec_z str_l output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows_2)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data_2 0 (Zlength (output_rows_2)) output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows_2)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) < INT_MAX) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (problem_1_spec_z str_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
.

Definition separate_paren_groups_partial_solve_wit_1_pure := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_paren_input_1 str_l )) (PreH4 : (paren_safe_input_1 str_l )) (PreH5 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH6 : (problem_1_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  (store_string paren_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition separate_paren_groups_partial_solve_wit_1_aux := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (PreH1 : (valid_string str_l )) (PreH2 : (all_ascii str_l )) (PreH3 : (valid_paren_input_1 str_l )) (PreH4 : (paren_safe_input_1 str_l )) (PreH5 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH6 : (problem_1_pre_z str_l )) ,
  (store_string paren_string_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ”
  &&  (store_string paren_string_pre str_l )
.

Definition separate_paren_groups_partial_solve_wit_1 := separate_paren_groups_partial_solve_wit_1_pure -> separate_paren_groups_partial_solve_wit_1_aux.

Definition separate_paren_groups_partial_solve_wit_2 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_paren_input_1 str_l )) (PreH6 : (paren_safe_input_1 str_l )) (PreH7 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH8 : (problem_1_pre_z str_l )) ,
  (store_string paren_string_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ”
  &&  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition separate_paren_groups_partial_solve_wit_3_pure := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_input_1 str_l )) (PreH7 : (paren_safe_input_1 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_1_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition separate_paren_groups_partial_solve_wit_3_aux := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (valid_string str_l )) (PreH5 : (all_ascii str_l )) (PreH6 : (valid_paren_input_1 str_l )) (PreH7 : (paren_safe_input_1 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_1_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition separate_paren_groups_partial_solve_wit_3 := separate_paren_groups_partial_solve_wit_3_pure -> separate_paren_groups_partial_solve_wit_3_aux.

Definition separate_paren_groups_partial_solve_wit_4_pure := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((( &( "row" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "paren_string" ) )) # Ptr  |-> paren_string_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> ((i - start ) + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((((i - start ) + 1 ) + 1 ) > 0) ” 
  &&  “ ((((i - start ) + 1 ) + 1 ) < INT_MAX) ”
.

Definition separate_paren_groups_partial_solve_wit_4_aux := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (len: Z) (ch: Z) (start: Z) (level: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((level - 1 ) = 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 41)) (PreH3 : ((Znth i (c_string (str_l)) 0) <> 40)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= level)) (PreH15 : (level <= i)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_paren_input_1 str_l )) (PreH25 : (paren_safe_input_1 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_1_pre_z str_l )) (PreH28 : (paren_scan_state_1 str_l i level start output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
|--
  “ ((((i - start ) + 1 ) + 1 ) > 0) ” 
  &&  “ ((((i - start ) + 1 ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((level - 1 ) = 0) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) = 41) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <> 40) ” 
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
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ ((-1) <= start) ” 
  &&  “ (start < i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i level start output_rows ) ”
  &&  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
.

Definition separate_paren_groups_partial_solve_wit_4 := separate_paren_groups_partial_solve_wit_4_pure -> separate_paren_groups_partial_solve_wit_4_aux.

Definition separate_paren_groups_partial_solve_wit_5 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (row <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (ch = 41)) (PreH13 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH14 : (level = 0)) (PreH15 : (0 <= start)) (PreH16 : (start <= i)) (PreH17 : (len = ((i - start ) + 1 ))) (PreH18 : (0 <= k)) (PreH19 : (k <= len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i 1 start output_rows )) (PreH27 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg row k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len) ”
  &&  (((row + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i row k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
.

Definition separate_paren_groups_partial_solve_wit_6 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (k: Z) (len: Z) (start: Z) (level: Z) (ch: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (row: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (row <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (ch = 41)) (PreH13 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH14 : (level = 0)) (PreH15 : (0 <= start)) (PreH16 : (start <= i)) (PreH17 : (len = ((i - start ) + 1 ))) (PreH18 : (0 <= k)) (PreH19 : (k <= len)) (PreH20 : (valid_string str_l )) (PreH21 : (all_ascii str_l )) (PreH22 : (valid_paren_input_1 str_l )) (PreH23 : (paren_safe_input_1 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_1_pre_z str_l )) (PreH26 : (paren_scan_state_1 str_l i 1 start output_rows )) (PreH27 : ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg row k (len + 1 ) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (k >= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ” 
  &&  “ ((Zlength ((paren_payload_1 (str_l) (start) ((i + 1 ))))) = len) ”
  &&  (((row + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i row len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row k (paren_payload_1 (str_l) (start) ((start + k ))) )
.

Definition separate_paren_groups_partial_solve_wit_7 := 
forall (paren_string_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (row: Z) (out_size: Z) (ch: Z) (level: Z) (start: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (row <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (ch = 41)) (PreH12 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH13 : (level = 0)) (PreH14 : (0 <= start)) (PreH15 : (start <= i)) (PreH16 : (len = ((i - start ) + 1 ))) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_paren_input_1 str_l )) (PreH20 : (paren_safe_input_1 str_l )) (PreH21 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH22 : (problem_1_pre_z str_l )) (PreH23 : (paren_scan_state_1 str_l i 1 start output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string paren_string_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
|--
  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (row <> 0) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= i) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (ch = 41) ” 
  &&  “ (ch = (Znth (i) ((c_string (str_l))) (0))) ” 
  &&  “ (level = 0) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start <= i) ” 
  &&  “ (len = ((i - start ) + 1 )) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_paren_input_1 str_l ) ” 
  &&  “ (paren_safe_input_1 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_1_pre_z str_l ) ” 
  &&  “ (paren_scan_state_1 str_l i 1 start output_rows ) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full paren_string_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (paren_rows_heap_1 output_ptrs output_rows )
  **  (CharArray.full row (len + 1 ) (paren_row_1 (str_l) (start) ((i + 1 ))) )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_separate_paren_groups_safety_wit_1 : separate_paren_groups_safety_wit_1.
Axiom proof_of_separate_paren_groups_safety_wit_2 : separate_paren_groups_safety_wit_2.
Axiom proof_of_separate_paren_groups_safety_wit_3 : separate_paren_groups_safety_wit_3.
Axiom proof_of_separate_paren_groups_safety_wit_4 : separate_paren_groups_safety_wit_4.
Axiom proof_of_separate_paren_groups_safety_wit_5 : separate_paren_groups_safety_wit_5.
Axiom proof_of_separate_paren_groups_safety_wit_6 : separate_paren_groups_safety_wit_6.
Axiom proof_of_separate_paren_groups_safety_wit_7 : separate_paren_groups_safety_wit_7.
Axiom proof_of_separate_paren_groups_safety_wit_8 : separate_paren_groups_safety_wit_8.
Axiom proof_of_separate_paren_groups_safety_wit_9 : separate_paren_groups_safety_wit_9.
Axiom proof_of_separate_paren_groups_safety_wit_10 : separate_paren_groups_safety_wit_10.
Axiom proof_of_separate_paren_groups_safety_wit_11 : separate_paren_groups_safety_wit_11.
Axiom proof_of_separate_paren_groups_safety_wit_12 : separate_paren_groups_safety_wit_12.
Axiom proof_of_separate_paren_groups_safety_wit_13 : separate_paren_groups_safety_wit_13.
Axiom proof_of_separate_paren_groups_safety_wit_14 : separate_paren_groups_safety_wit_14.
Axiom proof_of_separate_paren_groups_safety_wit_15 : separate_paren_groups_safety_wit_15.
Axiom proof_of_separate_paren_groups_safety_wit_16 : separate_paren_groups_safety_wit_16.
Axiom proof_of_separate_paren_groups_safety_wit_17 : separate_paren_groups_safety_wit_17.
Axiom proof_of_separate_paren_groups_safety_wit_18 : separate_paren_groups_safety_wit_18.
Axiom proof_of_separate_paren_groups_safety_wit_19 : separate_paren_groups_safety_wit_19.
Axiom proof_of_separate_paren_groups_safety_wit_20 : separate_paren_groups_safety_wit_20.
Axiom proof_of_separate_paren_groups_safety_wit_21 : separate_paren_groups_safety_wit_21.
Axiom proof_of_separate_paren_groups_safety_wit_22 : separate_paren_groups_safety_wit_22.
Axiom proof_of_separate_paren_groups_safety_wit_23 : separate_paren_groups_safety_wit_23.
Axiom proof_of_separate_paren_groups_safety_wit_24 : separate_paren_groups_safety_wit_24.
Axiom proof_of_separate_paren_groups_safety_wit_25 : separate_paren_groups_safety_wit_25.
Axiom proof_of_separate_paren_groups_safety_wit_26 : separate_paren_groups_safety_wit_26.
Axiom proof_of_separate_paren_groups_safety_wit_27 : separate_paren_groups_safety_wit_27.
Axiom proof_of_separate_paren_groups_safety_wit_28 : separate_paren_groups_safety_wit_28.
Axiom proof_of_separate_paren_groups_safety_wit_29 : separate_paren_groups_safety_wit_29.
Axiom proof_of_separate_paren_groups_safety_wit_30 : separate_paren_groups_safety_wit_30.
Axiom proof_of_separate_paren_groups_safety_wit_31 : separate_paren_groups_safety_wit_31.
Axiom proof_of_separate_paren_groups_safety_wit_32 : separate_paren_groups_safety_wit_32.
Axiom proof_of_separate_paren_groups_safety_wit_33 : separate_paren_groups_safety_wit_33.
Axiom proof_of_separate_paren_groups_safety_wit_34 : separate_paren_groups_safety_wit_34.
Axiom proof_of_separate_paren_groups_safety_wit_35 : separate_paren_groups_safety_wit_35.
Axiom proof_of_separate_paren_groups_safety_wit_36 : separate_paren_groups_safety_wit_36.
Axiom proof_of_separate_paren_groups_entail_wit_1 : separate_paren_groups_entail_wit_1.
Axiom proof_of_separate_paren_groups_entail_wit_2_1 : separate_paren_groups_entail_wit_2_1.
Axiom proof_of_separate_paren_groups_entail_wit_2_2 : separate_paren_groups_entail_wit_2_2.
Axiom proof_of_separate_paren_groups_entail_wit_3 : separate_paren_groups_entail_wit_3.
Axiom proof_of_separate_paren_groups_entail_wit_4 : separate_paren_groups_entail_wit_4.
Axiom proof_of_separate_paren_groups_entail_wit_5 : separate_paren_groups_entail_wit_5.
Axiom proof_of_separate_paren_groups_entail_wit_6 : separate_paren_groups_entail_wit_6.
Axiom proof_of_separate_paren_groups_entail_wit_7 : separate_paren_groups_entail_wit_7.
Axiom proof_of_separate_paren_groups_entail_wit_8 : separate_paren_groups_entail_wit_8.
Axiom proof_of_separate_paren_groups_entail_wit_9_1 : separate_paren_groups_entail_wit_9_1.
Axiom proof_of_separate_paren_groups_entail_wit_9_2 : separate_paren_groups_entail_wit_9_2.
Axiom proof_of_separate_paren_groups_entail_wit_9_3 : separate_paren_groups_entail_wit_9_3.
Axiom proof_of_separate_paren_groups_entail_wit_9_4 : separate_paren_groups_entail_wit_9_4.
Axiom proof_of_separate_paren_groups_entail_wit_10 : separate_paren_groups_entail_wit_10.
Axiom proof_of_separate_paren_groups_return_wit_1 : separate_paren_groups_return_wit_1.
Axiom proof_of_separate_paren_groups_partial_solve_wit_1_pure : separate_paren_groups_partial_solve_wit_1_pure.
Axiom proof_of_separate_paren_groups_partial_solve_wit_1 : separate_paren_groups_partial_solve_wit_1.
Axiom proof_of_separate_paren_groups_partial_solve_wit_2 : separate_paren_groups_partial_solve_wit_2.
Axiom proof_of_separate_paren_groups_partial_solve_wit_3_pure : separate_paren_groups_partial_solve_wit_3_pure.
Axiom proof_of_separate_paren_groups_partial_solve_wit_3 : separate_paren_groups_partial_solve_wit_3.
Axiom proof_of_separate_paren_groups_partial_solve_wit_4_pure : separate_paren_groups_partial_solve_wit_4_pure.
Axiom proof_of_separate_paren_groups_partial_solve_wit_4 : separate_paren_groups_partial_solve_wit_4.
Axiom proof_of_separate_paren_groups_partial_solve_wit_5 : separate_paren_groups_partial_solve_wit_5.
Axiom proof_of_separate_paren_groups_partial_solve_wit_6 : separate_paren_groups_partial_solve_wit_6.
Axiom proof_of_separate_paren_groups_partial_solve_wit_7 : separate_paren_groups_partial_solve_wit_7.

End VC_Correct.
