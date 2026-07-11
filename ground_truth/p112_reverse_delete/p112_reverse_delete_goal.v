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
Require Import p112_reverse_delete.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function reverse_delete -----*)

Definition reverse_delete_safety_wit_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "pal" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_4 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "hit" ) )) # Ptr  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_5 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition reverse_delete_safety_wit_6 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_7 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (s_l)))) (PreH4 : (0 <= ((string_length (c_l)) + 1 ))) (PreH5 : (0 <= ((string_length (s_l)) + 1 ))) (PreH6 : (valid_string s_l )) (PreH7 : (valid_string c_l )) (PreH8 : (valid_reverse_delete_input_112 s_l c_l )) (PreH9 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (c_l)) < INT_MAX)) (PreH11 : (problem_112_pre_z s_l c_l )) ,
  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |-> retval_2)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_8 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (s_l)))) (PreH4 : (0 <= ((string_length (c_l)) + 1 ))) (PreH5 : (0 <= ((string_length (s_l)) + 1 ))) (PreH6 : (valid_string s_l )) (PreH7 : (valid_string c_l )) (PreH8 : (valid_reverse_delete_input_112 s_l c_l )) (PreH9 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (c_l)) < INT_MAX)) (PreH11 : (problem_112_pre_z s_l c_l )) ,
  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |-> retval_2)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_9 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_4)
  **  (PtrArray.undef_full retval_4 2 )
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |-> retval_2)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_10 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (s_l)))) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_l)))) (PreH11 : (filtered <> 0)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (pal = 1)) (PreH17 : (valid_string s_l )) (PreH18 : (valid_string c_l )) (PreH19 : (valid_reverse_delete_input_112 s_l c_l )) (PreH20 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (c_l)) < INT_MAX)) (PreH22 : (problem_112_pre_z s_l c_l )) (PreH23 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (store_string c_pre c_l )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_11 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> retval)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition reverse_delete_safety_wit_12 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (i: Z) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (0 <= k)) (PreH5 : (k <= (i + 1 ))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (hit = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_13 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (i: Z) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (hit <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_14 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (k = (Zlength (filtered_l)))) (PreH8 : (filtered <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_15 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_16 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= (k ÷ 2 ))) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (k = (Zlength (filtered_l)))) (PreH5 : (filtered <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (pal = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH20 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition reverse_delete_safety_wit_17 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= (k ÷ 2 ))) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (k = (Zlength (filtered_l)))) (PreH5 : (filtered <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (pal = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH20 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition reverse_delete_safety_wit_18 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= (k ÷ 2 ))) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (k = (Zlength (filtered_l)))) (PreH5 : (filtered <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (pal = 1)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH20 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_19 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= (k ÷ 2 ))) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (k = (Zlength (filtered_l)))) (PreH5 : (filtered <> 0)) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (pal = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH20 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition reverse_delete_safety_wit_20 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
).

Definition reverse_delete_safety_wit_20_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_20_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
.

Definition reverse_delete_safety_wit_21 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
).

Definition reverse_delete_safety_wit_21_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (((k - 1 ) - i ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_21_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= ((k - 1 ) - i )) ”
.

Definition reverse_delete_safety_wit_22 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
).

Definition reverse_delete_safety_wit_22_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_22_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition reverse_delete_safety_wit_23 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k - 1 )) ”
).

Definition reverse_delete_safety_wit_23_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((k - 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_23_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= (k - 1 )) ”
.

Definition reverse_delete_safety_wit_24 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_25 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i < (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_26 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_27 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_28 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition reverse_delete_safety_wit_28_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_28_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_29 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
).

Definition reverse_delete_safety_wit_29_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((i + 1 ) <= INT_MAX) ”
.

Definition reverse_delete_safety_wit_29_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition reverse_delete_safety_wit_30 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i >= (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_31 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i >= (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_32 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_33 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> 0)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_34 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 0)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((( &( "truth" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_35 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((( &( "truth" ) )) # Ptr  |->_)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition reverse_delete_safety_wit_36 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal = 0)) ,
  ((( &( "truth" ) )) # Ptr  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ False ”
.

Definition reverse_delete_safety_wit_37 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 0)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal <> 0)) ,
  ((( &( "truth" ) )) # Ptr  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ False ”
.

Definition reverse_delete_safety_wit_38 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (hit: Z) (ch: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (pal = 1)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) (PreH16 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH17 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "truth" ) )) # Ptr  |-> truth)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full truth 5 (bool_row_112 (true)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_safety_wit_39 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (hit: Z) (ch: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (pal = 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) (PreH16 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH17 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "truth" ) )) # Ptr  |-> truth)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full truth 6 (bool_row_112 (false)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition reverse_delete_entail_wit_1 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
|--
  EX (filtered_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (s_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (filtered_l))) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_4 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (1 = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l 0 filtered_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_4)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full retval_2 0 filtered_l )
  **  (CharArray.undef_seg retval_2 0 (retval + 1 ) )
  **  (PtrArray.undef_full retval_4 2 )
) \/
(
forall (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (filter_prefix_state_112 s_l c_l 0 (@nil Z) ) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (0 <= retval) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (PtrArray.undef_full retval_4 2 )
).

Definition reverse_delete_entail_wit_1_split_goal_1 := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (filter_prefix_state_112 s_l c_l 0 (@nil Z) ) ”
.

Definition reverse_delete_entail_wit_1_split_goal_2 := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 = (Zlength ((@nil Z)))) ”
.

Definition reverse_delete_entail_wit_1_split_goal_3 := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  “ (0 <= retval) ”
.

Definition reverse_delete_entail_wit_1_split_goal_spatial := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (retval_4: Z) (PreH1 : (retval_4 <> 0)) (PreH2 : (retval_3 <> 0)) (PreH3 : (retval_2 <> 0)) (PreH4 : (retval = (string_length (s_l)))) (PreH5 : (0 <= ((string_length (c_l)) + 1 ))) (PreH6 : (0 <= ((string_length (s_l)) + 1 ))) (PreH7 : (valid_string s_l )) (PreH8 : (valid_string c_l )) (PreH9 : (valid_reverse_delete_input_112 s_l c_l )) (PreH10 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH11 : ((string_length (c_l)) < INT_MAX)) (PreH12 : (problem_112_pre_z s_l c_l )) ,
  (PtrArray.undef_full retval_4 2 )
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
|--
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (PtrArray.undef_full retval_4 2 )
.

Definition reverse_delete_entail_wit_2 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= (i + 1 )) ” 
  &&  “ ((k + 1 ) = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered (k + 1 ) filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
) \/
(
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (filter_prefix_state_112 s_l c_l (i + 1 ) (app (filtered_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z))))) ) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ” 
  &&  “ ((k + 1 ) = (Zlength ((app (filtered_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z)))))))) ”
  &&  (PtrArray.undef_full data 2 )
).

Definition reverse_delete_entail_wit_2_split_goal_1 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (filter_prefix_state_112 s_l c_l (i + 1 ) (app (filtered_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z))))) ) ”
.

Definition reverse_delete_entail_wit_2_split_goal_2 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ ((Znth i (c_string (s_l)) 0) <= 127) ”
.

Definition reverse_delete_entail_wit_2_split_goal_3 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (0 <= (Znth i (c_string (s_l)) 0)) ”
.

Definition reverse_delete_entail_wit_2_split_goal_4 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ ((k + 1 ) = (Zlength ((app (filtered_l_2) ((cons ((signed_last_nbits ((Znth i (c_string (s_l)) 0)) (8))) ((@nil Z)))))))) ”
.

Definition reverse_delete_entail_wit_2_split_goal_spatial := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_entail_wit_3 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (store_string c_pre c_l )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l_2 )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (0 <= i) ” 
  &&  “ (i < n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
) \/
(
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l_2 ) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ”
  &&  (PtrArray.undef_full data 2 )
).

Definition reverse_delete_entail_wit_3_split_goal_1 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l_2 ) ”
.

Definition reverse_delete_entail_wit_3_split_goal_2 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ ((Znth i (c_string (s_l)) 0) <= 127) ”
.

Definition reverse_delete_entail_wit_3_split_goal_3 := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  “ (0 <= (Znth i (c_string (s_l)) 0)) ”
.

Definition reverse_delete_entail_wit_3_split_goal_spatial := 
forall (c_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l_2)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (PtrArray.undef_full data 2 )
|--
  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_entail_wit_4_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (i: Z) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (0 <= k)) (PreH5 : (k <= (i + 1 ))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (hit = 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l_2 )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (i + 1 )) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_entail_wit_4_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (i: Z) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (hit: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (s_l)))) (PreH4 : (0 <= k)) (PreH5 : (k <= i)) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (hit <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l_2 )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= (i + 1 )) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l (i + 1 ) filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_entail_wit_5 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (s_l)))) (PreH7 : (0 <= k)) (PreH8 : (k <= i)) (PreH9 : (k = (Zlength (filtered_l_2)))) (PreH10 : (filtered <> 0)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (pal = 1)) (PreH16 : (valid_string s_l )) (PreH17 : (valid_string c_l )) (PreH18 : (valid_reverse_delete_input_112 s_l c_l )) (PreH19 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH20 : ((string_length (c_l)) < INT_MAX)) (PreH21 : (problem_112_pre_z s_l c_l )) (PreH22 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l_2) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
) \/
(
forall (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (s_l)))) (PreH8 : (0 <= k)) (PreH9 : (k <= i)) (PreH10 : (k = (Zlength (filtered_l_2)))) (PreH11 : (filtered <> 0)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (pal = 1)) (PreH17 : (valid_string s_l )) (PreH18 : (valid_string c_l )) (PreH19 : (valid_reverse_delete_input_112 s_l c_l )) (PreH20 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (c_l)) < INT_MAX)) (PreH22 : (problem_112_pre_z s_l c_l )) (PreH23 : (filter_prefix_state_112 s_l c_l i filtered_l_2 )) ,
  (CharArray.full filtered (k + 1 ) (app (filtered_l_2) ((cons (0) ((@nil Z))))) )
  **  (PtrArray.undef_full data 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ”
  &&  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (PtrArray.undef_full data 2 )
).

Definition reverse_delete_entail_wit_6 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l_2)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l_2 )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l 0 pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l 0 pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
.

Definition reverse_delete_entail_wit_7_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l_2)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l_2)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH22 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l_2 )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
.

Definition reverse_delete_entail_wit_7_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l_2)) 0) = (Znth ((k - 1 ) - i ) (c_string (filtered_l_2)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH22 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l_2 )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (i + 1 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 ))
.

Definition reverse_delete_entail_wit_8_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : ((Znth i (c_string (filtered_l_2)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l_2)) 0))) (PreH5 : (i < (k ÷ 2 ))) (PreH6 : (0 <= i)) (PreH7 : (i <= (k ÷ 2 ))) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (k = (Zlength (filtered_l_2)))) (PreH10 : (filtered <> 0)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (pal = 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH25 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
.

Definition reverse_delete_entail_wit_8_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : ((Znth i (c_string (filtered_l_2)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l_2)) 0))) (PreH5 : (i < (k ÷ 2 ))) (PreH6 : (0 <= i)) (PreH7 : (i <= (k ÷ 2 ))) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (k = (Zlength (filtered_l_2)))) (PreH10 : (filtered <> 0)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (pal = 1)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH25 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) 0 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
.

Definition reverse_delete_entail_wit_8_3 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (i >= (k ÷ 2 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (k ÷ 2 ))) (PreH7 : (n = (string_length (s_l)))) (PreH8 : (k = (Zlength (filtered_l_2)))) (PreH9 : (filtered <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (pal = 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string s_l )) (PreH18 : (valid_string c_l )) (PreH19 : (valid_reverse_delete_input_112 s_l c_l )) (PreH20 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (c_l)) < INT_MAX)) (PreH22 : (problem_112_pre_z s_l c_l )) (PreH23 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH24 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
.

Definition reverse_delete_entail_wit_8_4 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (i >= (k ÷ 2 ))) (PreH5 : (0 <= i)) (PreH6 : (i <= (k ÷ 2 ))) (PreH7 : (n = (string_length (s_l)))) (PreH8 : (k = (Zlength (filtered_l_2)))) (PreH9 : (filtered <> 0)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (pal = 1)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (valid_string s_l )) (PreH18 : (valid_string c_l )) (PreH19 : (valid_reverse_delete_input_112 s_l c_l )) (PreH20 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH21 : ((string_length (c_l)) < INT_MAX)) (PreH22 : (problem_112_pre_z s_l c_l )) (PreH23 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH24 : (palindrome_scan_state_112 filtered_l_2 i pal )) ,
  (((data + (0 * sizeof(PTR) ) )) # Ptr  |-> filtered)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
|--
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
  ||
  (EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 ))
.

Definition reverse_delete_entail_wit_9_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 0)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal = 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_entail_wit_9_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal = 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_entail_wit_10_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 0)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_entail_wit_10_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal <> 0) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_entail_wit_11 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH20 : (palindrome_scan_state_112 filtered_l_2 (k ÷ 2 ) pal )) (PreH21 : (pal <> 0)) ,
  (CharArray.full retval 5 (bool_row_112 (true)) )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full retval 5 (bool_row_112 (true)) )
.

Definition reverse_delete_entail_wit_12 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (valid_string s_l )) (PreH14 : (valid_string c_l )) (PreH15 : (valid_reverse_delete_input_112 s_l c_l )) (PreH16 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH17 : ((string_length (c_l)) < INT_MAX)) (PreH18 : (problem_112_pre_z s_l c_l )) (PreH19 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH20 : (palindrome_scan_state_112 filtered_l_2 (k ÷ 2 ) pal )) (PreH21 : (pal = 0)) ,
  (CharArray.full retval 6 (bool_row_112 (false)) )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  EX (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full retval 6 (bool_row_112 (false)) )
.

Definition reverse_delete_entail_wit_13_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (ch: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (0 <= 6)) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH21 : (palindrome_scan_state_112 filtered_l_2 (k ÷ 2 ) pal )) ,
  (PtrArray.seg data 0 (1 + 1 ) (app ((cons (filtered) ((@nil Z)))) ((cons (truth) ((@nil Z))))) )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full truth 6 (bool_row_112 (false)) )
|--
  (EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (output_ptrs = (cons (filtered) ((cons (truth) ((@nil Z)))))) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) ))
  ||
  (EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (output_ptrs = (cons (filtered) ((cons (truth) ((@nil Z)))))) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) ))
.

Definition reverse_delete_entail_wit_13_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (ch: Z) (PreH1 : (0 <= ((string_length (filtered_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (0 <= 5)) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l_2)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l_2 )) (PreH21 : (palindrome_scan_state_112 filtered_l_2 (k ÷ 2 ) pal )) ,
  (PtrArray.seg data 0 (1 + 1 ) (app ((cons (filtered) ((@nil Z)))) ((cons (truth) ((@nil Z))))) )
  **  (CharArray.full filtered ((string_length (filtered_l_2)) + 1 ) (c_string (filtered_l_2)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (CharArray.full truth 5 (bool_row_112 (true)) )
|--
  (EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (output_ptrs = (cons (filtered) ((cons (truth) ((@nil Z)))))) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) ))
  ||
  (EX (output_rows: (@list (@list Z)))  (output_ptrs: (@list Z))  (filtered_l: (@list Z)) ,
  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (output_ptrs = (cons (filtered) ((cons (truth) ((@nil Z)))))) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) ))
.

Definition reverse_delete_return_wit_1 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (pal = 0)) (PreH10 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH11 : ((Zlength (output_rows_2)) = 2)) (PreH12 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH13 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data_2 0 2 output_ptrs_2 )
  **  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ ((Zlength (output_ptrs)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) )
) \/
(
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 0)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  “ ((Zlength (output_ptrs_2)) = 2) ”
  &&  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
).

Definition reverse_delete_return_wit_1_split_goal_1 := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 0)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  “ ((Zlength (output_ptrs_2)) = 2) ”
.

Definition reverse_delete_return_wit_1_split_goal_spatial := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 0)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
.

Definition reverse_delete_return_wit_2 := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data_2 <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (pal = 1)) (PreH10 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH11 : ((Zlength (output_rows_2)) = 2)) (PreH12 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH13 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data_2 0 2 output_ptrs_2 )
  **  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) = 2) ” 
  &&  “ ((Zlength (output_ptrs)) = 2) ” 
  &&  “ (output_rows = (reverse_delete_rows_112 (s_l) (c_l))) ” 
  &&  “ (problem_112_spec_z s_l c_l output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (PtrArray.seg data 0 2 output_ptrs )
  **  (CharArray.full (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) (Znth (0) (output_rows) ((@nil Z))) )
  **  (CharArray.undef_seg (Znth (0) (output_ptrs) (0)) (Zlength ((Znth (0) (output_rows) ((@nil Z))))) ((string_length (s_l)) + 1 ) )
  **  (CharArray.full (Znth (1) (output_ptrs) (0)) (Zlength ((Znth (1) (output_rows) ((@nil Z))))) (Znth (1) (output_rows) ((@nil Z))) )
) \/
(
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  “ ((Zlength (output_ptrs_2)) = 2) ”
  &&  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
).

Definition reverse_delete_return_wit_2_split_goal_1 := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  “ ((Zlength (output_ptrs_2)) = 2) ”
.

Definition reverse_delete_return_wit_2_split_goal_spatial := 
forall (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data_2: Z) (ch: Z) (pal: Z) (PreH1 : (0 <= ((string_length (c_l)) + 1 ))) (PreH2 : (0 <= ((string_length (s_l)) + 1 ))) (PreH3 : (0 <= (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))))) (PreH4 : (0 <= (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (truth <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data_2 <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (output_ptrs_2 = (cons (filtered) ((cons (truth) ((@nil Z))))))) (PreH15 : ((Zlength (output_rows_2)) = 2)) (PreH16 : (output_rows_2 = (reverse_delete_rows_112 (s_l) (c_l)))) (PreH17 : (problem_112_spec_z s_l c_l output_rows_2 )) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH25 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) (output_rows_2) ((@nil Z))))) (Znth (0) (output_rows_2) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) (output_rows_2) ((@nil Z))))) (Znth (1) (output_rows_2) ((@nil Z))) )
|--
  (CharArray.full (Znth (0) (output_ptrs_2) (0)) (Zlength ((Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (0) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
  **  (CharArray.full (Znth (1) (output_ptrs_2) (0)) (Zlength ((Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))))) (Znth (1) ((reverse_delete_rows_112 (s_l) (c_l))) ((@nil Z))) )
.

Definition reverse_delete_partial_solve_wit_1_pure := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (PreH1 : (valid_string s_l )) (PreH2 : (valid_string c_l )) (PreH3 : (valid_reverse_delete_input_112 s_l c_l )) (PreH4 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH5 : ((string_length (c_l)) < INT_MAX)) (PreH6 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
|--
  “ (valid_string s_l ) ” 
  &&  “ ((string_length (s_l)) < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_1_aux := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (PreH1 : (valid_string s_l )) (PreH2 : (valid_string c_l )) (PreH3 : (valid_reverse_delete_input_112 s_l c_l )) (PreH4 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH5 : ((string_length (c_l)) < INT_MAX)) (PreH6 : (problem_112_pre_z s_l c_l )) ,
  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
|--
  “ (valid_string s_l ) ” 
  &&  “ ((string_length (s_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ”
  &&  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
.

Definition reverse_delete_partial_solve_wit_1 := reverse_delete_partial_solve_wit_1_pure -> reverse_delete_partial_solve_wit_1_aux.

Definition reverse_delete_partial_solve_wit_2_pure := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (retval = (string_length (s_l)))) (PreH8 : (0 <= ((string_length (c_l)) + 1 ))) (PreH9 : (0 <= ((string_length (s_l)) + 1 ))) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) ,
  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
).

Definition reverse_delete_partial_solve_wit_2_pure_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval <= INT_MAX)) (PreH2 : (1 <= INT_MAX)) (PreH3 : (0 <= INT_MAX)) (PreH4 : (retval >= INT_MIN)) (PreH5 : (1 >= INT_MIN)) (PreH6 : (0 >= INT_MIN)) (PreH7 : (retval = (string_length (s_l)))) (PreH8 : (0 <= ((string_length (c_l)) + 1 ))) (PreH9 : (0 <= ((string_length (s_l)) + 1 ))) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) ,
  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |->_)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition reverse_delete_partial_solve_wit_2_aux := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (s_l)))) (PreH2 : (0 <= ((string_length (c_l)) + 1 ))) (PreH3 : (0 <= ((string_length (s_l)) + 1 ))) (PreH4 : (valid_string s_l )) (PreH5 : (valid_string c_l )) (PreH6 : (valid_reverse_delete_input_112 s_l c_l )) (PreH7 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH8 : ((string_length (c_l)) < INT_MAX)) (PreH9 : (problem_112_pre_z s_l c_l )) ,
  (store_string s_pre s_l )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
|--
  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ ((retval + 1 ) > 0) ” 
  &&  “ (retval = (string_length (s_l))) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ”
  &&  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
.

Definition reverse_delete_partial_solve_wit_2 := reverse_delete_partial_solve_wit_2_pure -> reverse_delete_partial_solve_wit_2_aux.

Definition reverse_delete_partial_solve_wit_3 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (s_l)))) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (valid_string s_l )) (PreH6 : (valid_string c_l )) (PreH7 : (valid_reverse_delete_input_112 s_l c_l )) (PreH8 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH9 : ((string_length (c_l)) < INT_MAX)) (PreH10 : (problem_112_pre_z s_l c_l )) ,
  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (s_l))) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
.

Definition reverse_delete_partial_solve_wit_4_pure := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (s_l)))) (PreH4 : (0 <= ((string_length (c_l)) + 1 ))) (PreH5 : (0 <= ((string_length (s_l)) + 1 ))) (PreH6 : (valid_string s_l )) (PreH7 : (valid_string c_l )) (PreH8 : (valid_reverse_delete_input_112 s_l c_l )) (PreH9 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (c_l)) < INT_MAX)) (PreH11 : (problem_112_pre_z s_l c_l )) ,
  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  ((( &( "out" ) )) # Ptr  |-> retval_3)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "filtered" ) )) # Ptr  |-> retval_2)
  **  ((( &( "hit" ) )) # Ptr  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "pal" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= 2) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition reverse_delete_partial_solve_wit_4_aux := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (s_l)))) (PreH4 : (0 <= ((string_length (c_l)) + 1 ))) (PreH5 : (0 <= ((string_length (s_l)) + 1 ))) (PreH6 : (valid_string s_l )) (PreH7 : (valid_string c_l )) (PreH8 : (valid_reverse_delete_input_112 s_l c_l )) (PreH9 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH10 : ((string_length (c_l)) < INT_MAX)) (PreH11 : (problem_112_pre_z s_l c_l )) ,
  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
|--
  “ (0 <= 2) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (s_l))) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ”
  &&  ((&((retval_3)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_3)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
.

Definition reverse_delete_partial_solve_wit_4 := reverse_delete_partial_solve_wit_4_pure -> reverse_delete_partial_solve_wit_4_aux.

Definition reverse_delete_partial_solve_wit_5_pure := 
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (k = (Zlength (filtered_l)))) (PreH8 : (filtered <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (valid_string c_l ) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ”
) \/
(
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (2 <= INT_MAX)) (PreH2 : (pal <= INT_MAX)) (PreH3 : ((Znth i (c_string (s_l)) 0) <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (2 >= INT_MIN)) (PreH8 : (pal >= INT_MIN)) (PreH9 : ((Znth i (c_string (s_l)) 0) >= INT_MIN)) (PreH10 : (k >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (c_l)) + 1 ))) (PreH14 : (0 <= ((string_length (s_l)) + 1 ))) (PreH15 : (i < n)) (PreH16 : (0 <= i)) (PreH17 : (i <= n)) (PreH18 : (n = (string_length (s_l)))) (PreH19 : (0 <= k)) (PreH20 : (k <= i)) (PreH21 : (k = (Zlength (filtered_l)))) (PreH22 : (filtered <> 0)) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (pal = 1)) (PreH28 : (valid_string s_l )) (PreH29 : (valid_string c_l )) (PreH30 : (valid_reverse_delete_input_112 s_l c_l )) (PreH31 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH32 : ((string_length (c_l)) < INT_MAX)) (PreH33 : (problem_112_pre_z s_l c_l )) (PreH34 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= (Znth i (c_string (s_l)) 0)) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ”
).

Definition reverse_delete_partial_solve_wit_5_pure_split_goal_1 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (2 <= INT_MAX)) (PreH2 : (pal <= INT_MAX)) (PreH3 : ((Znth i (c_string (s_l)) 0) <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (2 >= INT_MIN)) (PreH8 : (pal >= INT_MIN)) (PreH9 : ((Znth i (c_string (s_l)) 0) >= INT_MIN)) (PreH10 : (k >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (c_l)) + 1 ))) (PreH14 : (0 <= ((string_length (s_l)) + 1 ))) (PreH15 : (i < n)) (PreH16 : (0 <= i)) (PreH17 : (i <= n)) (PreH18 : (n = (string_length (s_l)))) (PreH19 : (0 <= k)) (PreH20 : (k <= i)) (PreH21 : (k = (Zlength (filtered_l)))) (PreH22 : (filtered <> 0)) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (pal = 1)) (PreH28 : (valid_string s_l )) (PreH29 : (valid_string c_l )) (PreH30 : (valid_reverse_delete_input_112 s_l c_l )) (PreH31 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH32 : ((string_length (c_l)) < INT_MAX)) (PreH33 : (problem_112_pre_z s_l c_l )) (PreH34 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= (Znth i (c_string (s_l)) 0)) ”
.

Definition reverse_delete_partial_solve_wit_5_pure_split_goal_2 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (hit: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (2 <= INT_MAX)) (PreH2 : (pal <= INT_MAX)) (PreH3 : ((Znth i (c_string (s_l)) 0) <= INT_MAX)) (PreH4 : (k <= INT_MAX)) (PreH5 : (n <= INT_MAX)) (PreH6 : (i <= INT_MAX)) (PreH7 : (2 >= INT_MIN)) (PreH8 : (pal >= INT_MIN)) (PreH9 : ((Znth i (c_string (s_l)) 0) >= INT_MIN)) (PreH10 : (k >= INT_MIN)) (PreH11 : (n >= INT_MIN)) (PreH12 : (i >= INT_MIN)) (PreH13 : (0 <= ((string_length (c_l)) + 1 ))) (PreH14 : (0 <= ((string_length (s_l)) + 1 ))) (PreH15 : (i < n)) (PreH16 : (0 <= i)) (PreH17 : (i <= n)) (PreH18 : (n = (string_length (s_l)))) (PreH19 : (0 <= k)) (PreH20 : (k <= i)) (PreH21 : (k = (Zlength (filtered_l)))) (PreH22 : (filtered <> 0)) (PreH23 : (out <> 0)) (PreH24 : (data <> 0)) (PreH25 : (0 <= ch)) (PreH26 : (ch <= 127)) (PreH27 : (pal = 1)) (PreH28 : (valid_string s_l )) (PreH29 : (valid_string c_l )) (PreH30 : (valid_reverse_delete_input_112 s_l c_l )) (PreH31 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH32 : ((string_length (c_l)) < INT_MAX)) (PreH33 : (problem_112_pre_z s_l c_l )) (PreH34 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "c" ) )) # Ptr  |-> c_pre)
  **  ((( &( "filtered" ) )) # Ptr  |-> filtered)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "hit" ) )) # Ptr  |-> hit)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (s_l)) 0))
  **  ((( &( "pal" ) )) # Int  |-> pal)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ ((Znth i (c_string (s_l)) 0) <= 127) ”
.

Definition reverse_delete_partial_solve_wit_5_aux := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (k = (Zlength (filtered_l)))) (PreH8 : (filtered <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (valid_string c_l ) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ ((Znth i (c_string (s_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (s_l)) 0)) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l i filtered_l ) ”
  &&  (store_string c_pre c_l )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_partial_solve_wit_5 := reverse_delete_partial_solve_wit_5_pure -> reverse_delete_partial_solve_wit_5_aux.

Definition reverse_delete_partial_solve_wit_6 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre )) (PreH3 : (0 <= ((string_length (c_l)) + 1 ))) (PreH4 : (0 <= ((string_length (s_l)) + 1 ))) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (s_l)))) (PreH9 : (0 <= k)) (PreH10 : (k <= i)) (PreH11 : (k = (Zlength (filtered_l)))) (PreH12 : (filtered <> 0)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (pal = 1)) (PreH18 : (valid_string s_l )) (PreH19 : (valid_string c_l )) (PreH20 : (valid_reverse_delete_input_112 s_l c_l )) (PreH21 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH22 : ((string_length (c_l)) < INT_MAX)) (PreH23 : (problem_112_pre_z s_l c_l )) (PreH24 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  (store_string c_pre c_l )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (retval = 0) ” 
  &&  “ (strchr_result c_l (Znth i (c_string (s_l)) 0) retval c_pre ) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l i filtered_l ) ”
  &&  (((filtered + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.undef_missing_i filtered k k (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_partial_solve_wit_7 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (k: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (0 <= k)) (PreH6 : (k <= i)) (PreH7 : (k = (Zlength (filtered_l)))) (PreH8 : (filtered <> 0)) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (pal = 1)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l i filtered_l )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (CharArray.full filtered k filtered_l )
  **  (CharArray.undef_seg filtered k (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (i >= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= i) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l i filtered_l ) ”
  &&  (((filtered + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  (CharArray.undef_missing_i filtered k k (n + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.full filtered k filtered_l )
  **  (PtrArray.undef_full data 2 )
.

Definition reverse_delete_partial_solve_wit_8 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i >= (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 1)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (i >= (k ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l i pal ) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_9 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : (i >= (k ÷ 2 ))) (PreH2 : (0 <= i)) (PreH3 : (i <= (k ÷ 2 ))) (PreH4 : (n = (string_length (s_l)))) (PreH5 : (k = (Zlength (filtered_l)))) (PreH6 : (filtered <> 0)) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (pal = 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (valid_string s_l )) (PreH15 : (valid_string c_l )) (PreH16 : (valid_reverse_delete_input_112 s_l c_l )) (PreH17 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH18 : ((string_length (c_l)) < INT_MAX)) (PreH19 : (problem_112_pre_z s_l c_l )) (PreH20 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH21 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (i >= (k ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l i pal ) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_10 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 1)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0)) ” 
  &&  “ (i < (k ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l i pal ) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_11 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (pal: Z) (ch: Z) (data: Z) (out: Z) (filtered: Z) (filtered_l: (@list Z)) (n: Z) (k: Z) (i: Z) (PreH1 : ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0))) (PreH2 : (i < (k ÷ 2 ))) (PreH3 : (0 <= i)) (PreH4 : (i <= (k ÷ 2 ))) (PreH5 : (n = (string_length (s_l)))) (PreH6 : (k = (Zlength (filtered_l)))) (PreH7 : (filtered <> 0)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (pal = 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (valid_string s_l )) (PreH16 : (valid_string c_l )) (PreH17 : (valid_reverse_delete_input_112 s_l c_l )) (PreH18 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH19 : ((string_length (c_l)) < INT_MAX)) (PreH20 : (problem_112_pre_z s_l c_l )) (PreH21 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH22 : (palindrome_scan_state_112 filtered_l i pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.undef_full data 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ ((Znth i (c_string (filtered_l)) 0) <> (Znth ((k - 1 ) - i ) (c_string (filtered_l)) 0)) ” 
  &&  “ (i < (k ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (k ÷ 2 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l i pal ) ”
  &&  (((data + (0 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_missing_i data 0 0 2 )
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
.

Definition reverse_delete_partial_solve_wit_12 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 1)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal <> 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 1) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal <> 0) ”
  &&  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_partial_solve_wit_13 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (ch: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (pal = 1)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) (PreH16 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH17 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full truth 5 (bool_row_112 (true)) )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (0 <= 5) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (pal = 1) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  (((data + (1 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (CharArray.full truth 5 (bool_row_112 (true)) )
.

Definition reverse_delete_partial_solve_wit_14 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (out: Z) (data: Z) (ch: Z) (pal: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (pal = 0)) (PreH9 : (valid_string s_l )) (PreH10 : (valid_string c_l )) (PreH11 : (valid_reverse_delete_input_112 s_l c_l )) (PreH12 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH13 : ((string_length (c_l)) < INT_MAX)) (PreH14 : (problem_112_pre_z s_l c_l )) (PreH15 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH16 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) (PreH17 : (pal = 0)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (pal = 0) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ” 
  &&  “ (pal = 0) ”
  &&  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
.

Definition reverse_delete_partial_solve_wit_15 := 
forall (c_pre: Z) (s_pre: Z) (c_l: (@list Z)) (s_l: (@list Z)) (filtered_l: (@list Z)) (n: Z) (k: Z) (filtered: Z) (truth: Z) (out: Z) (data: Z) (pal: Z) (ch: Z) (PreH1 : (n = (string_length (s_l)))) (PreH2 : (k = (Zlength (filtered_l)))) (PreH3 : (filtered <> 0)) (PreH4 : (truth <> 0)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (pal = 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (valid_string s_l )) (PreH11 : (valid_string c_l )) (PreH12 : (valid_reverse_delete_input_112 s_l c_l )) (PreH13 : (((string_length (s_l)) + 2 ) < INT_MAX)) (PreH14 : ((string_length (c_l)) < INT_MAX)) (PreH15 : (problem_112_pre_z s_l c_l )) (PreH16 : (filter_prefix_state_112 s_l c_l n filtered_l )) (PreH17 : (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (store_string s_pre s_l )
  **  (store_string c_pre c_l )
  **  (store_string filtered filtered_l )
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (PtrArray.undef_seg data 1 2 )
  **  (CharArray.full truth 6 (bool_row_112 (false)) )
|--
  “ (0 <= ((string_length (filtered_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (c_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length (s_l)) + 1 )) ” 
  &&  “ (0 <= 6) ” 
  &&  “ (n = (string_length (s_l))) ” 
  &&  “ (k = (Zlength (filtered_l))) ” 
  &&  “ (filtered <> 0) ” 
  &&  “ (truth <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (pal = 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (valid_string s_l ) ” 
  &&  “ (valid_string c_l ) ” 
  &&  “ (valid_reverse_delete_input_112 s_l c_l ) ” 
  &&  “ (((string_length (s_l)) + 2 ) < INT_MAX) ” 
  &&  “ ((string_length (c_l)) < INT_MAX) ” 
  &&  “ (problem_112_pre_z s_l c_l ) ” 
  &&  “ (filter_prefix_state_112 s_l c_l n filtered_l ) ” 
  &&  “ (palindrome_scan_state_112 filtered_l (k ÷ 2 ) pal ) ”
  &&  (((data + (1 * sizeof(PTR) ) )) # Ptr  |->_)
  **  (CharArray.full filtered ((string_length (filtered_l)) + 1 ) (c_string (filtered_l)) )
  **  (CharArray.full c_pre ((string_length (c_l)) + 1 ) (c_string (c_l)) )
  **  (CharArray.full s_pre ((string_length (s_l)) + 1 ) (c_string (s_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
  **  (CharArray.undef_seg filtered (k + 1 ) (n + 1 ) )
  **  (PtrArray.seg data 0 1 (cons (filtered) ((@nil Z))) )
  **  (CharArray.full truth 6 (bool_row_112 (false)) )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_reverse_delete_safety_wit_1 : reverse_delete_safety_wit_1.
Axiom proof_of_reverse_delete_safety_wit_2 : reverse_delete_safety_wit_2.
Axiom proof_of_reverse_delete_safety_wit_3 : reverse_delete_safety_wit_3.
Axiom proof_of_reverse_delete_safety_wit_4 : reverse_delete_safety_wit_4.
Axiom proof_of_reverse_delete_safety_wit_5 : reverse_delete_safety_wit_5.
Axiom proof_of_reverse_delete_safety_wit_6 : reverse_delete_safety_wit_6.
Axiom proof_of_reverse_delete_safety_wit_7 : reverse_delete_safety_wit_7.
Axiom proof_of_reverse_delete_safety_wit_8 : reverse_delete_safety_wit_8.
Axiom proof_of_reverse_delete_safety_wit_9 : reverse_delete_safety_wit_9.
Axiom proof_of_reverse_delete_safety_wit_10 : reverse_delete_safety_wit_10.
Axiom proof_of_reverse_delete_safety_wit_11 : reverse_delete_safety_wit_11.
Axiom proof_of_reverse_delete_safety_wit_12 : reverse_delete_safety_wit_12.
Axiom proof_of_reverse_delete_safety_wit_13 : reverse_delete_safety_wit_13.
Axiom proof_of_reverse_delete_safety_wit_14 : reverse_delete_safety_wit_14.
Axiom proof_of_reverse_delete_safety_wit_15 : reverse_delete_safety_wit_15.
Axiom proof_of_reverse_delete_safety_wit_16 : reverse_delete_safety_wit_16.
Axiom proof_of_reverse_delete_safety_wit_17 : reverse_delete_safety_wit_17.
Axiom proof_of_reverse_delete_safety_wit_18 : reverse_delete_safety_wit_18.
Axiom proof_of_reverse_delete_safety_wit_19 : reverse_delete_safety_wit_19.
Axiom proof_of_reverse_delete_safety_wit_20 : reverse_delete_safety_wit_20.
Axiom proof_of_reverse_delete_safety_wit_21 : reverse_delete_safety_wit_21.
Axiom proof_of_reverse_delete_safety_wit_22 : reverse_delete_safety_wit_22.
Axiom proof_of_reverse_delete_safety_wit_23 : reverse_delete_safety_wit_23.
Axiom proof_of_reverse_delete_safety_wit_24 : reverse_delete_safety_wit_24.
Axiom proof_of_reverse_delete_safety_wit_25 : reverse_delete_safety_wit_25.
Axiom proof_of_reverse_delete_safety_wit_26 : reverse_delete_safety_wit_26.
Axiom proof_of_reverse_delete_safety_wit_27 : reverse_delete_safety_wit_27.
Axiom proof_of_reverse_delete_safety_wit_28 : reverse_delete_safety_wit_28.
Axiom proof_of_reverse_delete_safety_wit_29 : reverse_delete_safety_wit_29.
Axiom proof_of_reverse_delete_safety_wit_30 : reverse_delete_safety_wit_30.
Axiom proof_of_reverse_delete_safety_wit_31 : reverse_delete_safety_wit_31.
Axiom proof_of_reverse_delete_safety_wit_32 : reverse_delete_safety_wit_32.
Axiom proof_of_reverse_delete_safety_wit_33 : reverse_delete_safety_wit_33.
Axiom proof_of_reverse_delete_safety_wit_34 : reverse_delete_safety_wit_34.
Axiom proof_of_reverse_delete_safety_wit_35 : reverse_delete_safety_wit_35.
Axiom proof_of_reverse_delete_safety_wit_36 : reverse_delete_safety_wit_36.
Axiom proof_of_reverse_delete_safety_wit_37 : reverse_delete_safety_wit_37.
Axiom proof_of_reverse_delete_safety_wit_38 : reverse_delete_safety_wit_38.
Axiom proof_of_reverse_delete_safety_wit_39 : reverse_delete_safety_wit_39.
Axiom proof_of_reverse_delete_entail_wit_1 : reverse_delete_entail_wit_1.
Axiom proof_of_reverse_delete_entail_wit_2 : reverse_delete_entail_wit_2.
Axiom proof_of_reverse_delete_entail_wit_3 : reverse_delete_entail_wit_3.
Axiom proof_of_reverse_delete_entail_wit_4_1 : reverse_delete_entail_wit_4_1.
Axiom proof_of_reverse_delete_entail_wit_4_2 : reverse_delete_entail_wit_4_2.
Axiom proof_of_reverse_delete_entail_wit_5 : reverse_delete_entail_wit_5.
Axiom proof_of_reverse_delete_entail_wit_6 : reverse_delete_entail_wit_6.
Axiom proof_of_reverse_delete_entail_wit_7_1 : reverse_delete_entail_wit_7_1.
Axiom proof_of_reverse_delete_entail_wit_7_2 : reverse_delete_entail_wit_7_2.
Axiom proof_of_reverse_delete_entail_wit_8_1 : reverse_delete_entail_wit_8_1.
Axiom proof_of_reverse_delete_entail_wit_8_2 : reverse_delete_entail_wit_8_2.
Axiom proof_of_reverse_delete_entail_wit_8_3 : reverse_delete_entail_wit_8_3.
Axiom proof_of_reverse_delete_entail_wit_8_4 : reverse_delete_entail_wit_8_4.
Axiom proof_of_reverse_delete_entail_wit_9_1 : reverse_delete_entail_wit_9_1.
Axiom proof_of_reverse_delete_entail_wit_9_2 : reverse_delete_entail_wit_9_2.
Axiom proof_of_reverse_delete_entail_wit_10_1 : reverse_delete_entail_wit_10_1.
Axiom proof_of_reverse_delete_entail_wit_10_2 : reverse_delete_entail_wit_10_2.
Axiom proof_of_reverse_delete_entail_wit_11 : reverse_delete_entail_wit_11.
Axiom proof_of_reverse_delete_entail_wit_12 : reverse_delete_entail_wit_12.
Axiom proof_of_reverse_delete_entail_wit_13_1 : reverse_delete_entail_wit_13_1.
Axiom proof_of_reverse_delete_entail_wit_13_2 : reverse_delete_entail_wit_13_2.
Axiom proof_of_reverse_delete_return_wit_1 : reverse_delete_return_wit_1.
Axiom proof_of_reverse_delete_return_wit_2 : reverse_delete_return_wit_2.
Axiom proof_of_reverse_delete_partial_solve_wit_1_pure : reverse_delete_partial_solve_wit_1_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_1 : reverse_delete_partial_solve_wit_1.
Axiom proof_of_reverse_delete_partial_solve_wit_2_pure : reverse_delete_partial_solve_wit_2_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_2 : reverse_delete_partial_solve_wit_2.
Axiom proof_of_reverse_delete_partial_solve_wit_3 : reverse_delete_partial_solve_wit_3.
Axiom proof_of_reverse_delete_partial_solve_wit_4_pure : reverse_delete_partial_solve_wit_4_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_4 : reverse_delete_partial_solve_wit_4.
Axiom proof_of_reverse_delete_partial_solve_wit_5_pure : reverse_delete_partial_solve_wit_5_pure.
Axiom proof_of_reverse_delete_partial_solve_wit_5 : reverse_delete_partial_solve_wit_5.
Axiom proof_of_reverse_delete_partial_solve_wit_6 : reverse_delete_partial_solve_wit_6.
Axiom proof_of_reverse_delete_partial_solve_wit_7 : reverse_delete_partial_solve_wit_7.
Axiom proof_of_reverse_delete_partial_solve_wit_8 : reverse_delete_partial_solve_wit_8.
Axiom proof_of_reverse_delete_partial_solve_wit_9 : reverse_delete_partial_solve_wit_9.
Axiom proof_of_reverse_delete_partial_solve_wit_10 : reverse_delete_partial_solve_wit_10.
Axiom proof_of_reverse_delete_partial_solve_wit_11 : reverse_delete_partial_solve_wit_11.
Axiom proof_of_reverse_delete_partial_solve_wit_12 : reverse_delete_partial_solve_wit_12.
Axiom proof_of_reverse_delete_partial_solve_wit_13 : reverse_delete_partial_solve_wit_13.
Axiom proof_of_reverse_delete_partial_solve_wit_14 : reverse_delete_partial_solve_wit_14.
Axiom proof_of_reverse_delete_partial_solve_wit_15 : reverse_delete_partial_solve_wit_15.

End VC_Correct.
