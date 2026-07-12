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
Require Import p149_sorted_list_sum.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function cmp_word -----*)

(*----- Function sorted_list_sum -----*)

Definition sorted_list_sum_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre <= 100)) (PreH4 : (rows_well_formed_149 rows lst_size_pre )) (PreH5 : (problem_149_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  ((( &( "output_size" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "output_size" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows )) (PreH14 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ ((retval <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition sorted_list_sum_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows )) (PreH14 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition sorted_list_sum_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows)))) (PreH8 : (output_size = (Zlength (output_ptrs)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows )) (PreH14 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "len" ) )) # Int  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition sorted_list_sum_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (output_rows_next: (@list (@list Z))) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows)))) (PreH7 : (output_size = (Zlength (output_ptrs)))) (PreH8 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows )) (PreH14 : (filter_even_step_take_149 rows i output_rows output_rows_next )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) lst_size_pre )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ ((output_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (output_size + 1 )) ”
.

Definition sorted_list_sum_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (output_rows_next: (@list (@list Z))) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows)))) (PreH7 : (output_size = (Zlength (output_ptrs)))) (PreH8 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows )) (PreH14 : (filter_even_step_take_149 rows i output_rows output_rows_next )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) lst_size_pre )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition sorted_list_sum_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (cur: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows (i + 1 ) output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sorted_list_sum_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (cur: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows (i + 1 ) output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition sorted_list_sum_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength (output_ptrs))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows 0 output_rows ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg retval_2 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_149 rows lst_size_pre )) (PreH6 : (problem_149_pre_z rows )) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (Zlength (output_rows))) ” 
  &&  “ (0 = (Zlength ((@nil Z)))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows 0 output_rows ) ”
  &&  emp
).

Definition sorted_list_sum_entail_wit_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows i output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (row_ptr: Z)  (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (output_size: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (0 <= output_size)) (PreH6 : (output_size <= i)) (PreH7 : (output_size = (Zlength (output_rows_2)))) (PreH8 : (output_size = (Zlength (output_ptrs_2)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows_2 )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition sorted_list_sum_entail_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_149 rows lst_size_pre )) (PreH10 : (problem_149_pre_z rows )) (PreH11 : (filter_even_state_149 rows i output_rows_2 )) (PreH12 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) (PreH14 : ((Zlength ((Znth (i) (rows) ((@nil Z))))) = ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
.

Definition sorted_list_sum_entail_wit_4 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : ((retval % ( 2 ) ) = 0)) (PreH2 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_149 rows lst_size_pre )) (PreH13 : (problem_149_pre_z rows )) (PreH14 : (filter_even_state_149 rows i output_rows_2 )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_rows_next: (@list (@list Z)))  (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (filter_even_step_take_149 rows i output_rows output_rows_next ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : ((retval % ( 2 ) ) = 0)) (PreH2 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_149 rows lst_size_pre )) (PreH13 : (problem_149_pre_z rows )) (PreH14 : (filter_even_state_149 rows i output_rows_2 )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  TT && emp 
|--
  EX (output_rows_next: (@list (@list Z)))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (filter_even_step_take_149 rows i output_rows output_rows_next ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  emp
).

Definition sorted_list_sum_entail_wit_5 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_rows_next: (@list (@list Z))) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows_2 )) (PreH14 : (filter_even_step_take_149 rows i output_rows_2 output_rows_next )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (PtrArray.seg data 0 (output_size + 1 ) (app (output_ptrs_2) ((cons (row_ptr) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (output_size + 1 ) lst_size_pre )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 (output_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (output_size + 1 ) lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_rows_next: (@list (@list Z))) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows_2 )) (PreH14 : (filter_even_step_take_149 rows i output_rows_2 output_rows_next )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= (output_size + 1 )) ” 
  &&  “ ((output_size + 1 ) <= (i + 1 )) ” 
  &&  “ ((output_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((output_size + 1 ) = (Zlength ((app (output_ptrs_2) ((cons (row_ptr) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full lst_pre lst_size_pre rows )
).

Definition sorted_list_sum_entail_wit_6 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : ((retval % ( 2 ) ) <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_149 rows lst_size_pre )) (PreH13 : (problem_149_pre_z rows )) (PreH14 : (filter_even_state_149 rows i output_rows_2 )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (filter_even_step_keep_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : ((retval % ( 2 ) ) <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (0 <= output_size)) (PreH7 : (output_size <= i)) (PreH8 : (output_size = (Zlength (output_rows_2)))) (PreH9 : (output_size = (Zlength (output_ptrs_2)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (rows_well_formed_149 rows lst_size_pre )) (PreH13 : (problem_149_pre_z rows )) (PreH14 : (filter_even_state_149 rows i output_rows_2 )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  TT && emp 
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (retval = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (filter_even_step_keep_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  emp
).

Definition sorted_list_sum_entail_wit_7 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows i output_rows_2 )) (PreH13 : (filter_even_step_keep_149 rows i output_rows_2 )) (PreH14 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH2 : (0 <= i)) (PreH3 : (i < lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows_2)))) (PreH7 : (output_size = (Zlength (output_ptrs_2)))) (PreH8 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (rows_well_formed_149 rows lst_size_pre )) (PreH12 : (problem_149_pre_z rows )) (PreH13 : (filter_even_state_149 rows i output_rows_2 )) (PreH14 : (filter_even_step_keep_149 rows i output_rows_2 )) (PreH15 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  (CharPtrArray2.full lst_pre lst_size_pre rows )
).

Definition sorted_list_sum_entail_wit_8_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows (i + 1 ) output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
.

Definition sorted_list_sum_entail_wit_8_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= (i + 1 ))) (PreH5 : (output_size = (Zlength (output_rows_2)))) (PreH6 : (output_size = (Zlength (output_ptrs_2)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows (i + 1 ) output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= (i + 1 )) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows (i + 1 ) output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
.

Definition sorted_list_sum_entail_wit_9 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (sorted_ptrs_2: (@list Z)) (sorted_rows_2: (@list (@list Z))) (PreH1 : (output_size = (rows_length (sorted_rows_2)))) (PreH2 : (output_size = (ptrs_length (sorted_ptrs_2)))) (PreH3 : (string_rows_sorted sorted_rows_2 )) (PreH4 : (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows_2 )) (PreH5 : (i >= lst_size_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= lst_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_rows)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_149 rows lst_size_pre )) (PreH15 : (problem_149_pre_z rows )) (PreH16 : (filter_even_state_149 rows i output_rows )) ,
  (PtrArray.seg data 0 output_size sorted_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  EX (sorted_ptrs: (@list Z))  (sorted_rows: (@list (@list Z)))  (filtered_rows: (@list (@list Z))) ,
  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (output_size = (Zlength (filtered_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows lst_size_pre filtered_rows ) ” 
  &&  “ (string_rows_sorted sorted_rows ) ” 
  &&  “ (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows ) ” 
  &&  “ (problem_149_spec_z_of_sorted_prefix rows sorted_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size sorted_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (sorted_ptrs_2: (@list Z)) (sorted_rows_2: (@list (@list Z))) (PreH1 : (output_size = (rows_length (sorted_rows_2)))) (PreH2 : (output_size = (ptrs_length (sorted_ptrs_2)))) (PreH3 : (string_rows_sorted sorted_rows_2 )) (PreH4 : (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows_2 )) (PreH5 : (i >= lst_size_pre)) (PreH6 : (0 <= i)) (PreH7 : (i <= lst_size_pre)) (PreH8 : (0 <= output_size)) (PreH9 : (output_size <= i)) (PreH10 : (output_size = (Zlength (output_rows)))) (PreH11 : (output_size = (Zlength (output_ptrs)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (rows_well_formed_149 rows lst_size_pre )) (PreH15 : (problem_149_pre_z rows )) (PreH16 : (filter_even_state_149 rows i output_rows )) ,
  TT && emp 
|--
  EX (sorted_rows: (@list (@list Z)))  (filtered_rows: (@list (@list Z))) ,
  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (output_size = (Zlength (filtered_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_ptrs_2))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows lst_size_pre filtered_rows ) ” 
  &&  “ (string_rows_sorted sorted_rows ) ” 
  &&  “ (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows ) ” 
  &&  “ (problem_149_spec_z_of_sorted_prefix rows sorted_rows ) ”
  &&  emp
).

Definition sorted_list_sum_entail_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (filtered_rows_2: (@list (@list Z))) (sorted_rows_2: (@list (@list Z))) (sorted_ptrs_2: (@list Z)) (output_size: Z) (out: Z) (data: Z) (PreH1 : (0 <= output_size)) (PreH2 : (output_size <= lst_size_pre)) (PreH3 : (output_size = (Zlength (filtered_rows_2)))) (PreH4 : (output_size = (Zlength (sorted_rows_2)))) (PreH5 : (output_size = (Zlength (sorted_ptrs_2)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (rows_well_formed_149 rows lst_size_pre )) (PreH9 : (problem_149_pre_z rows )) (PreH10 : (filter_even_state_149 rows lst_size_pre filtered_rows_2 )) (PreH11 : (string_rows_sorted sorted_rows_2 )) (PreH12 : (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows_2 )) (PreH13 : (problem_149_spec_z_of_sorted_prefix rows sorted_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size sorted_ptrs_2 )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  EX (sorted_ptrs: (@list Z))  (sorted_rows: (@list (@list Z)))  (filtered_rows: (@list (@list Z))) ,
  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (output_size = (Zlength (filtered_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_rows))) ” 
  &&  “ (output_size = (Zlength (sorted_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows lst_size_pre filtered_rows ) ” 
  &&  “ (string_rows_sorted sorted_rows ) ” 
  &&  “ (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows ) ” 
  &&  “ (problem_149_spec_z_of_sorted_prefix rows sorted_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size sorted_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
.

Definition sorted_list_sum_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (filtered_rows: (@list (@list Z))) (sorted_rows: (@list (@list Z))) (sorted_ptrs: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (PreH1 : (0 <= output_size_2)) (PreH2 : (output_size_2 <= lst_size_pre)) (PreH3 : (output_size_2 = (Zlength (filtered_rows)))) (PreH4 : (output_size_2 = (Zlength (sorted_rows)))) (PreH5 : (output_size_2 = (Zlength (sorted_ptrs)))) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (rows_well_formed_149 rows lst_size_pre )) (PreH9 : (problem_149_pre_z rows )) (PreH10 : (filter_even_state_149 rows lst_size_pre filtered_rows )) (PreH11 : (string_rows_sorted sorted_rows )) (PreH12 : (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows )) (PreH13 : (problem_149_spec_z_of_sorted_prefix rows sorted_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size_2)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data_2 0 output_size_2 sorted_ptrs )
  **  (PtrArray.undef_seg data_2 output_size_2 lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (problem_149_spec_z rows output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (filtered_rows: (@list (@list Z))) (sorted_rows: (@list (@list Z))) (sorted_ptrs: (@list Z)) (output_size_2: Z) (out: Z) (data_2: Z) (PreH1 : (0 <= output_size_2)) (PreH2 : (output_size_2 <= lst_size_pre)) (PreH3 : (output_size_2 = (Zlength (filtered_rows)))) (PreH4 : (output_size_2 = (Zlength (sorted_rows)))) (PreH5 : (output_size_2 = (Zlength (sorted_ptrs)))) (PreH6 : (out <> 0)) (PreH7 : (data_2 <> 0)) (PreH8 : (rows_well_formed_149 rows lst_size_pre )) (PreH9 : (problem_149_pre_z rows )) (PreH10 : (filter_even_state_149 rows lst_size_pre filtered_rows )) (PreH11 : (string_rows_sorted sorted_rows )) (PreH12 : (Permutation (filter_even_prefix_149 (rows) (lst_size_pre)) sorted_rows )) (PreH13 : (problem_149_spec_z_of_sorted_prefix rows sorted_rows )) ,
  (PtrArray.seg data_2 0 output_size_2 sorted_ptrs )
  **  (PtrArray.undef_seg data_2 output_size_2 lst_size_pre )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (output_size_2 = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_rows)) <= lst_size_pre) ” 
  &&  “ ((Zlength (output_rows)) = (Zlength (output_ptrs))) ” 
  &&  “ (problem_149_spec_z rows output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) lst_size_pre )
).

Definition sorted_list_sum_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre <= 100)) (PreH3 : (rows_well_formed_149 rows lst_size_pre )) (PreH4 : (problem_149_pre_z rows )) ,
  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= 100) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ”
  &&  (CharPtrArray2.full lst_pre lst_size_pre rows )
.

Definition sorted_list_sum_partial_solve_wit_2_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre <= 100)) (PreH4 : (rows_well_formed_149 rows lst_size_pre )) (PreH5 : (problem_149_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition sorted_list_sum_partial_solve_wit_2_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre <= 100)) (PreH4 : (rows_well_formed_149 rows lst_size_pre )) (PreH5 : (problem_149_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= 100) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
.

Definition sorted_list_sum_partial_solve_wit_2 := sorted_list_sum_partial_solve_wit_2_pure -> sorted_list_sum_partial_solve_wit_2_aux.

Definition sorted_list_sum_partial_solve_wit_3_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (len: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_149 rows lst_size_pre )) (PreH10 : (problem_149_pre_z rows )) (PreH11 : (filter_even_state_149 rows i output_rows )) (PreH12 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition sorted_list_sum_partial_solve_wit_3_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (output_size: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (rows_well_formed_149 rows lst_size_pre )) (PreH10 : (problem_149_pre_z rows )) (PreH11 : (filter_even_state_149 rows i output_rows )) (PreH12 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
.

Definition sorted_list_sum_partial_solve_wit_3 := sorted_list_sum_partial_solve_wit_3_pure -> sorted_list_sum_partial_solve_wit_3_aux.

Definition sorted_list_sum_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (output_rows_next: (@list (@list Z))) (i: Z) (output_size: Z) (len: Z) (out: Z) (data: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= output_size)) (PreH4 : (output_size <= i)) (PreH5 : (output_size = (Zlength (output_rows)))) (PreH6 : (output_size = (Zlength (output_ptrs)))) (PreH7 : (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows i output_rows )) (PreH13 : (filter_even_step_take_149 rows i output_rows output_rows_next )) (PreH14 : (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (0 <= ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (len = (string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ” 
  &&  “ (filter_even_step_take_149 rows i output_rows output_rows_next ) ” 
  &&  “ (valid_string (row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (((data + (output_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (output_size + 1 ) lst_size_pre )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_149 ((Znth (i) (rows) ((@nil Z))))))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (PtrArray.seg data 0 output_size output_ptrs )
.

Definition sorted_list_sum_partial_solve_wit_5_pure := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (len: Z) (cur: Z) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows)))) (PreH7 : (output_size = (Zlength (output_ptrs)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows i output_rows )) ,
  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (sizeof(PTR) = sizeof(PTR)) ” 
  &&  “ (output_size = (ptrs_length (output_ptrs))) ” 
  &&  “ (output_size = (rows_length ((filter_even_prefix_149 (rows) (lst_size_pre))))) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (len: Z) (cur: Z) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (lst_size_pre <= INT_MAX)) (PreH4 : (output_size <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (lst_size_pre >= INT_MIN)) (PreH8 : (output_size >= INT_MIN)) (PreH9 : (i >= lst_size_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_rows)))) (PreH15 : (output_size = (Zlength (output_ptrs)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (rows_well_formed_149 rows lst_size_pre )) (PreH19 : (problem_149_pre_z rows )) (PreH20 : (filter_even_state_149 rows i output_rows )) ,
  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (output_size = (rows_length ((filter_even_prefix_149 (rows) (lst_size_pre))))) ” 
  &&  “ (output_size = (ptrs_length (output_ptrs))) ”
).

Definition sorted_list_sum_partial_solve_wit_5_pure_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (len: Z) (cur: Z) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (lst_size_pre <= INT_MAX)) (PreH4 : (output_size <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (lst_size_pre >= INT_MIN)) (PreH8 : (output_size >= INT_MIN)) (PreH9 : (i >= lst_size_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_rows)))) (PreH15 : (output_size = (Zlength (output_ptrs)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (rows_well_formed_149 rows lst_size_pre )) (PreH19 : (problem_149_pre_z rows )) (PreH20 : (filter_even_state_149 rows i output_rows )) ,
  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (lst_size_pre < INT_MAX) ”
.

Definition sorted_list_sum_partial_solve_wit_5_pure_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (len: Z) (cur: Z) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (lst_size_pre <= INT_MAX)) (PreH4 : (output_size <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (lst_size_pre >= INT_MIN)) (PreH8 : (output_size >= INT_MIN)) (PreH9 : (i >= lst_size_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_rows)))) (PreH15 : (output_size = (Zlength (output_ptrs)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (rows_well_formed_149 rows lst_size_pre )) (PreH19 : (problem_149_pre_z rows )) (PreH20 : (filter_even_state_149 rows i output_rows )) ,
  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (output_size = (rows_length ((filter_even_prefix_149 (rows) (lst_size_pre))))) ”
.

Definition sorted_list_sum_partial_solve_wit_5_pure_split_goal_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (len: Z) (cur: Z) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (0 <= INT_MAX)) (PreH2 : (len <= INT_MAX)) (PreH3 : (lst_size_pre <= INT_MAX)) (PreH4 : (output_size <= INT_MAX)) (PreH5 : (0 >= INT_MIN)) (PreH6 : (len >= INT_MIN)) (PreH7 : (lst_size_pre >= INT_MIN)) (PreH8 : (output_size >= INT_MIN)) (PreH9 : (i >= lst_size_pre)) (PreH10 : (0 <= i)) (PreH11 : (i <= lst_size_pre)) (PreH12 : (0 <= output_size)) (PreH13 : (output_size <= i)) (PreH14 : (output_size = (Zlength (output_rows)))) (PreH15 : (output_size = (Zlength (output_ptrs)))) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (rows_well_formed_149 rows lst_size_pre )) (PreH19 : (problem_149_pre_z rows )) (PreH20 : (filter_even_state_149 rows i output_rows )) ,
  ((( &( "output_size" ) )) # Int  |-> output_size)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (output_size = (ptrs_length (output_ptrs))) ”
.

Definition sorted_list_sum_partial_solve_wit_5_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (data: Z) (out: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (output_size: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (0 <= output_size)) (PreH5 : (output_size <= i)) (PreH6 : (output_size = (Zlength (output_rows)))) (PreH7 : (output_size = (Zlength (output_ptrs)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (rows_well_formed_149 rows lst_size_pre )) (PreH11 : (problem_149_pre_z rows )) (PreH12 : (filter_even_state_149 rows i output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
|--
  “ (data <> 0) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= lst_size_pre) ” 
  &&  “ (sizeof(PTR) = sizeof(PTR)) ” 
  &&  “ (output_size = (ptrs_length (output_ptrs))) ” 
  &&  “ (output_size = (rows_length ((filter_even_prefix_149 (rows) (lst_size_pre))))) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (i >= lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (0 <= output_size) ” 
  &&  “ (output_size <= i) ” 
  &&  “ (output_size = (Zlength (output_rows))) ” 
  &&  “ (output_size = (Zlength (output_ptrs))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_149 rows lst_size_pre ) ” 
  &&  “ (problem_149_pre_z rows ) ” 
  &&  “ (filter_even_state_149 rows i output_rows ) ”
  &&  (PtrArray.seg data 0 output_size output_ptrs )
  **  (PtrArray.undef_seg data output_size lst_size_pre )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
.

Definition sorted_list_sum_partial_solve_wit_5 := sorted_list_sum_partial_solve_wit_5_pure -> sorted_list_sum_partial_solve_wit_5_aux.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_sorted_list_sum_safety_wit_1 : sorted_list_sum_safety_wit_1.
Axiom proof_of_sorted_list_sum_safety_wit_2 : sorted_list_sum_safety_wit_2.
Axiom proof_of_sorted_list_sum_safety_wit_3 : sorted_list_sum_safety_wit_3.
Axiom proof_of_sorted_list_sum_safety_wit_4 : sorted_list_sum_safety_wit_4.
Axiom proof_of_sorted_list_sum_safety_wit_5 : sorted_list_sum_safety_wit_5.
Axiom proof_of_sorted_list_sum_safety_wit_6 : sorted_list_sum_safety_wit_6.
Axiom proof_of_sorted_list_sum_safety_wit_7 : sorted_list_sum_safety_wit_7.
Axiom proof_of_sorted_list_sum_safety_wit_8 : sorted_list_sum_safety_wit_8.
Axiom proof_of_sorted_list_sum_safety_wit_9 : sorted_list_sum_safety_wit_9.
Axiom proof_of_sorted_list_sum_safety_wit_10 : sorted_list_sum_safety_wit_10.
Axiom proof_of_sorted_list_sum_safety_wit_11 : sorted_list_sum_safety_wit_11.
Axiom proof_of_sorted_list_sum_safety_wit_12 : sorted_list_sum_safety_wit_12.
Axiom proof_of_sorted_list_sum_entail_wit_1 : sorted_list_sum_entail_wit_1.
Axiom proof_of_sorted_list_sum_entail_wit_2 : sorted_list_sum_entail_wit_2.
Axiom proof_of_sorted_list_sum_entail_wit_3 : sorted_list_sum_entail_wit_3.
Axiom proof_of_sorted_list_sum_entail_wit_4 : sorted_list_sum_entail_wit_4.
Axiom proof_of_sorted_list_sum_entail_wit_5 : sorted_list_sum_entail_wit_5.
Axiom proof_of_sorted_list_sum_entail_wit_6 : sorted_list_sum_entail_wit_6.
Axiom proof_of_sorted_list_sum_entail_wit_7 : sorted_list_sum_entail_wit_7.
Axiom proof_of_sorted_list_sum_entail_wit_8_1 : sorted_list_sum_entail_wit_8_1.
Axiom proof_of_sorted_list_sum_entail_wit_8_2 : sorted_list_sum_entail_wit_8_2.
Axiom proof_of_sorted_list_sum_entail_wit_9 : sorted_list_sum_entail_wit_9.
Axiom proof_of_sorted_list_sum_entail_wit_10 : sorted_list_sum_entail_wit_10.
Axiom proof_of_sorted_list_sum_return_wit_1 : sorted_list_sum_return_wit_1.
Axiom proof_of_sorted_list_sum_partial_solve_wit_1 : sorted_list_sum_partial_solve_wit_1.
Axiom proof_of_sorted_list_sum_partial_solve_wit_2_pure : sorted_list_sum_partial_solve_wit_2_pure.
Axiom proof_of_sorted_list_sum_partial_solve_wit_2 : sorted_list_sum_partial_solve_wit_2.
Axiom proof_of_sorted_list_sum_partial_solve_wit_3_pure : sorted_list_sum_partial_solve_wit_3_pure.
Axiom proof_of_sorted_list_sum_partial_solve_wit_3 : sorted_list_sum_partial_solve_wit_3.
Axiom proof_of_sorted_list_sum_partial_solve_wit_4 : sorted_list_sum_partial_solve_wit_4.
Axiom proof_of_sorted_list_sum_partial_solve_wit_5_pure : sorted_list_sum_partial_solve_wit_5_pure.
Axiom proof_of_sorted_list_sum_partial_solve_wit_5 : sorted_list_sum_partial_solve_wit_5.

End VC_Correct.
