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
Require Import p113_odd_count.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function odd_count -----*)

Definition odd_count_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "numlen" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "outlen" ) )) # Int  |->_)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "t" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  (store_stringLit (LitMap (("the number of odd elements in the string i of the input."%string))) ("the number of odd elements in the string i of the input."%string) )
  **  (GlobalStrings_missing LitMap (cons (("the number of odd elements in the string i of the input."%string)) ((@nil string))) )
  **  ((( &( "tpl" ) )) # Ptr  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "numbuf" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("the number of odd elements in the string i of the input."%string))) ("the number of odd elements in the string i of the input."%string) )
  **  (GlobalStrings_missing LitMap (cons (("the number of odd elements in the string i of the input."%string)) ((@nil string))) )
  **  ((( &( "tpl" ) )) # Ptr  |-> ((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition odd_count_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre <= 100)) (PreH6 : (rows_well_formed_113 rows lst_size_pre )) (PreH7 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH8 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH9 : (problem_113_pre_z rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_3 32 )
  **  (GlobalStrings LitMap )
  **  ((( &( "numbuf" ) )) # Ptr  |-> retval_3)
  **  ((( &( "tpl" ) )) # Ptr  |-> ((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= sum)) (PreH10 : (sum < INT_MAX)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= numlen)) (PreH14 : (numlen < 32)) (PreH15 : (0 <= outlen)) (PreH16 : (outlen < INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < INT_MAX)) (PreH19 : (0 <= t)) (PreH20 : (t <= template_len_113)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) (PreH27 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH28 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH29 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= sum)) (PreH10 : (sum < INT_MAX)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= numlen)) (PreH14 : (numlen < 32)) (PreH15 : (0 <= outlen)) (PreH16 : (outlen < INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < INT_MAX)) (PreH19 : (0 <= t)) (PreH20 : (t <= template_len_113)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) (PreH27 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH28 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH29 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  ((( &( "j" ) )) # Int  |->_)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j < n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH7 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= j)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition odd_count_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= j)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= numlen)) (PreH16 : (numlen < 32)) (PreH17 : (0 <= outlen)) (PreH18 : (outlen < INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < INT_MAX)) (PreH21 : (0 <= t)) (PreH22 : (t <= template_len_113)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition odd_count_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition odd_count_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition odd_count_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) = 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((sum + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + 1 )) ”
.

Definition odd_count_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) = 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_21 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) = 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition odd_count_safety_wit_22 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) > 57)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition odd_count_safety_wit_23 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) < 48)) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= j)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= numlen)) (PreH16 : (numlen < 32)) (PreH17 : (0 <= outlen)) (PreH18 : (outlen < INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < INT_MAX)) (PreH21 : (0 <= t)) (PreH22 : (t <= template_len_113)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition odd_count_safety_wit_24 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) <> 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0))
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition odd_count_safety_wit_25 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((56 + (4 * (retval - 1 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (56 + (4 * (retval - 1 ) ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((56 + (4 * (retval - 1 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (56 + (4 * (retval - 1 ) ) )) ”
).

Definition odd_count_safety_wit_25_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((56 + (4 * (retval - 1 ) ) ) <= INT_MAX) ”
.

Definition odd_count_safety_wit_25_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((INT_MIN) <= (56 + (4 * (retval - 1 ) ) )) ”
.

Definition odd_count_safety_wit_26 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((4 * (retval - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * (retval - 1 ) )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((4 * (retval - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (4 * (retval - 1 ) )) ”
).

Definition odd_count_safety_wit_26_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((4 * (retval - 1 ) ) <= INT_MAX) ”
.

Definition odd_count_safety_wit_26_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((INT_MIN) <= (4 * (retval - 1 ) )) ”
.

Definition odd_count_safety_wit_27 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
).

Definition odd_count_safety_wit_27_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((retval - 1 ) <= INT_MAX) ”
.

Definition odd_count_safety_wit_27_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition odd_count_safety_wit_28 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (56 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 56) ”
.

Definition odd_count_safety_wit_29 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition odd_count_safety_wit_30 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_31 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "row_out" ) )) # Ptr  |->_)
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> (56 + (4 * (retval - 1 ) ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (((56 + (4 * (retval - 1 ) ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((56 + (4 * (retval - 1 ) ) ) + 1 )) ”
.

Definition odd_count_safety_wit_32 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "row_out" ) )) # Ptr  |->_)
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> (56 + (4 * (retval - 1 ) ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_33 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= 1)) (PreH3 : (0 <= retval)) (PreH4 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH5 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum < INT_MAX)) (PreH12 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.undef_full retval_2 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  ((( &( "row_out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> (56 + (4 * (retval - 1 ) ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_34 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= 1)) (PreH3 : (0 <= retval)) (PreH4 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH5 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum < INT_MAX)) (PreH12 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.undef_full retval_2 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  ((( &( "row_out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> (56 + (4 * (retval - 1 ) ) ))
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_35 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= t)) (PreH2 : (t <= template_len_113)) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH8 : (0 <= outlen)) (PreH9 : (outlen < INT_MAX)) (PreH10 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH11 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH12 : (0 <= k)) (PreH13 : (k <= outlen)) (PreH14 : (row_out <> 0)) (PreH15 : (out <> 0)) (PreH16 : (data <> 0)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (rows_well_formed_113 rows lst_size_pre )) (PreH20 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH21 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH22 : (problem_113_pre_z rows )) (PreH23 : (odd_count_state_113 rows i output_rows )) (PreH24 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (56 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 56) ”
.

Definition odd_count_safety_wit_36 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (t < 56)) (PreH2 : (0 <= t)) (PreH3 : (t <= template_len_113)) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH7 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH8 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH9 : (0 <= outlen)) (PreH10 : (outlen < INT_MAX)) (PreH11 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH12 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH13 : (0 <= k)) (PreH14 : (k <= outlen)) (PreH15 : (row_out <> 0)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0))
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition odd_count_safety_wit_37 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((k + numlen ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + numlen )) ”
.

Definition odd_count_safety_wit_38 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0))
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition odd_count_safety_wit_39 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0))
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_40 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + numlen ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + numlen ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
).

Definition odd_count_safety_wit_40_split_goal_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + numlen ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((t + 1 ) <= INT_MAX) ”
.

Definition odd_count_safety_wit_40_split_goal_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + numlen ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition odd_count_safety_wit_41 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + numlen ))
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_42 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0))
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((t + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (t + 1 )) ”
.

Definition odd_count_safety_wit_43 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0))
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition odd_count_safety_wit_44 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (t >= 56)) (PreH2 : (0 <= t)) (PreH3 : (t <= template_len_113)) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH7 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH8 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH9 : (0 <= outlen)) (PreH10 : (outlen < INT_MAX)) (PreH11 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH12 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH13 : (0 <= k)) (PreH14 : (k <= outlen)) (PreH15 : (row_out <> 0)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition odd_count_safety_wit_45 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= numlen)) (PreH5 : (t >= 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (PtrArray.seg data 0 (i + 1 ) (app (output_ptrs) ((cons (row_out) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition odd_count_entail_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre <= 100)) (PreH6 : (rows_well_formed_113 rows lst_size_pre )) (PreH7 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH8 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH9 : (problem_113_pre_z rows )) ,
  (CharArray.undef_full retval_3 32 )
  **  (GlobalStrings LitMap )
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 32) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows 0 output_rows ) ” 
  &&  “ ((Zlength (output_ptrs)) = 0) ” 
  &&  “ (((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ) = (LitMap (template_literal_113))) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg retval_2 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_2 0 lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full retval_3 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit ((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ) template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval <> 0)) (PreH4 : (0 <= lst_size_pre)) (PreH5 : (lst_size_pre <= 100)) (PreH6 : (rows_well_formed_113 rows lst_size_pre )) (PreH7 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH8 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH9 : (problem_113_pre_z rows )) ,
  (CharArray.undef_full retval_3 32 )
  **  (GlobalStrings LitMap )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 32) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows 0 output_rows ) ” 
  &&  “ ((Zlength ((@nil Z))) = 0) ” 
  &&  “ (((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ) = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 (@nil Z) output_rows )
  **  (CharArray.undef_full retval_3 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit ((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ) template_literal_113 )
).

Definition odd_count_entail_wit_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (sum: Z) (n: Z) (data: Z) (out: Z) (i: Z) (PreH1 : (i < lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : (0 <= sum)) (PreH9 : (sum < INT_MAX)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (0 <= numlen)) (PreH13 : (numlen < 32)) (PreH14 : (0 <= outlen)) (PreH15 : (outlen < INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < INT_MAX)) (PreH18 : (0 <= t)) (PreH19 : (t <= template_len_113)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows_2 )) (PreH25 : ((Zlength (output_ptrs_2)) = i)) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (row_ptr: Z)  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ” 
  &&  “ (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) ) ” 
  &&  “ ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX) ” 
  &&  “ ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (sum: Z) (n: Z) (data: Z) (out: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH2 : (i < lst_size_pre)) (PreH3 : (0 <= i)) (PreH4 : (i <= lst_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= sum)) (PreH10 : (sum < INT_MAX)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= numlen)) (PreH14 : (numlen < 32)) (PreH15 : (0 <= outlen)) (PreH16 : (outlen < INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < INT_MAX)) (PreH19 : (0 <= t)) (PreH20 : (t <= template_len_113)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows_2 )) (PreH26 : ((Zlength (output_ptrs_2)) = i)) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ” 
  &&  “ (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) ) ” 
  &&  “ ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX) ” 
  &&  “ ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= sum)) (PreH10 : (sum < INT_MAX)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= numlen)) (PreH14 : (numlen < 32)) (PreH15 : (0 <= outlen)) (PreH16 : (outlen < INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < INT_MAX)) (PreH19 : (0 <= t)) (PreH20 : (t <= template_len_113)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows_2 )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) (PreH27 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH28 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH29 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (0 = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= n)) (PreH8 : (n < INT_MAX)) (PreH9 : (0 <= sum)) (PreH10 : (sum < INT_MAX)) (PreH11 : (0 <= ch)) (PreH12 : (ch <= 127)) (PreH13 : (0 <= numlen)) (PreH14 : (numlen < 32)) (PreH15 : (0 <= outlen)) (PreH16 : (outlen < INT_MAX)) (PreH17 : (0 <= k)) (PreH18 : (k < INT_MAX)) (PreH19 : (0 <= t)) (PreH20 : (t <= template_len_113)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows_2 )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) (PreH27 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH28 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH29 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (retval = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (0 = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (0))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_4_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) = 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows_2 )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ ((sum + 1 ) = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) = 1)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH4 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH5 : (j < n)) (PreH6 : (0 <= j)) (PreH7 : (j <= n)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= j)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= numlen)) (PreH19 : (numlen < 32)) (PreH20 : (0 <= outlen)) (PreH21 : (outlen < INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < INT_MAX)) (PreH24 : (0 <= t)) (PreH25 : (t <= template_len_113)) (PreH26 : (rows_well_formed_113 rows lst_size_pre )) (PreH27 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH29 : (problem_113_pre_z rows )) (PreH30 : (odd_count_state_113 rows i output_rows_2 )) (PreH31 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ ((sum + 1 ) = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_4_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) > 57)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) > 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows_2 )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_4_3 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) < 48)) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= j)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= numlen)) (PreH16 : (numlen < 32)) (PreH17 : (0 <= outlen)) (PreH18 : (outlen < INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < INT_MAX)) (PreH21 : (0 <= t)) (PreH22 : (t <= template_len_113)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows_2 )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) < 48)) (PreH3 : (j < n)) (PreH4 : (0 <= j)) (PreH5 : (j <= n)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH10 : (0 <= sum)) (PreH11 : (sum <= j)) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= numlen)) (PreH17 : (numlen < 32)) (PreH18 : (0 <= outlen)) (PreH19 : (outlen < INT_MAX)) (PreH20 : (0 <= k)) (PreH21 : (k < INT_MAX)) (PreH22 : (0 <= t)) (PreH23 : (t <= template_len_113)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_4_4 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) <> 1)) (PreH2 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH4 : (j < n)) (PreH5 : (0 <= j)) (PreH6 : (j <= n)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH11 : (0 <= sum)) (PreH12 : (sum <= j)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows_2 )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) % ( 2 ) ) <> 1)) (PreH3 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 57)) (PreH4 : ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) >= 48)) (PreH5 : (j < n)) (PreH6 : (0 <= j)) (PreH7 : (j <= n)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH12 : (0 <= sum)) (PreH13 : (sum <= j)) (PreH14 : (out <> 0)) (PreH15 : (data <> 0)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= numlen)) (PreH19 : (numlen < 32)) (PreH20 : (0 <= outlen)) (PreH21 : (outlen < INT_MAX)) (PreH22 : (0 <= k)) (PreH23 : (k < INT_MAX)) (PreH24 : (0 <= t)) (PreH25 : (t <= template_len_113)) (PreH26 : (rows_well_formed_113 rows lst_size_pre )) (PreH27 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH28 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH29 : (problem_113_pre_z rows )) (PreH30 : (odd_count_state_113 rows i output_rows_2 )) (PreH31 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) ((j + 1 )))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (j + 1 )) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0)) ” 
  &&  “ ((Znth j (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) 0) <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_5 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (row_ptr: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (j >= n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH7 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH8 : (0 <= sum)) (PreH9 : (sum <= j)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows_2 )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (data: Z) (out: Z) (sum: Z) (i: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (j >= n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_prefix_113 ((row_payload_z_113 ((row_at_113 (i) (rows))))) (j)))) (PreH9 : (0 <= sum)) (PreH10 : (sum <= j)) (PreH11 : (out <> 0)) (PreH12 : (data <> 0)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= numlen)) (PreH16 : (numlen < 32)) (PreH17 : (0 <= outlen)) (PreH18 : (outlen < INT_MAX)) (PreH19 : (0 <= k)) (PreH20 : (k < INT_MAX)) (PreH21 : (0 <= t)) (PreH22 : (t <= template_len_113)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows_2 )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_6 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= 1)) (PreH3 : (0 <= retval)) (PreH4 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH5 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum < INT_MAX)) (PreH12 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows_2 )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.undef_full retval_2 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (out_l: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (retval = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= (56 + (4 * (retval - 1 ) ) )) ” 
  &&  “ ((56 + (4 * (retval - 1 ) ) ) < INT_MAX) ” 
  &&  “ ((56 + (4 * (retval - 1 ) ) ) = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 0 (decimal_digits_113 (sum)) 0 out_l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (56 + (4 * (retval - 1 ) ) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (0 <= 1)) (PreH3 : (0 <= retval)) (PreH4 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH5 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (0 <= sum)) (PreH11 : (sum < INT_MAX)) (PreH12 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= numlen)) (PreH18 : (numlen < 32)) (PreH19 : (0 <= outlen)) (PreH20 : (outlen < INT_MAX)) (PreH21 : (0 <= k)) (PreH22 : (k < INT_MAX)) (PreH23 : (0 <= t)) (PreH24 : (t <= template_len_113)) (PreH25 : (rows_well_formed_113 rows lst_size_pre )) (PreH26 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH27 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH28 : (problem_113_pre_z rows )) (PreH29 : (odd_count_state_113 rows i output_rows_2 )) (PreH30 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (CharArray.undef_full retval_2 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (retval = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= (56 + (4 * (retval - 1 ) ) )) ” 
  &&  “ ((56 + (4 * (retval - 1 ) ) ) < INT_MAX) ” 
  &&  “ ((56 + (4 * (retval - 1 ) ) ) = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 0 (decimal_digits_113 (sum)) 0 (@nil Z) ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (56 + (4 * (retval - 1 ) ) )) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharArray.undef_full retval_2 ((56 + (4 * (retval - 1 ) ) ) + 1 ) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_7 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l_2: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) = 105)) (PreH2 : (t < 56)) (PreH3 : (0 <= t)) (PreH4 : (t <= template_len_113)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH9 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH10 : (0 <= outlen)) (PreH11 : (outlen < INT_MAX)) (PreH12 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH13 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH14 : (0 <= k)) (PreH15 : (k <= outlen)) (PreH16 : (row_out <> 0)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows_2 )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l_2 )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (out_l: (@list Z)) ,
  “ (0 <= t) ” 
  &&  “ (t < template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (all_ascii (decimal_digits_113 (sum)) ) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l ) ” 
  &&  “ (0 <= k) ” 
  &&  “ ((k + numlen ) <= outlen) ” 
  &&  “ ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) = 105) ” 
  &&  “ ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_full (row_out + (k * sizeof(CHAR) ) ) numlen )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (tpl_v: Z) (k: Z) (out_l_2: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) = 105)) (PreH3 : (t < 56)) (PreH4 : (0 <= t)) (PreH5 : (t <= template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (0 <= outlen)) (PreH12 : (outlen < INT_MAX)) (PreH13 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH14 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH15 : (0 <= k)) (PreH16 : (k <= outlen)) (PreH17 : (row_out <> 0)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows_2 )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= t) ” 
  &&  “ (t < template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (all_ascii (decimal_digits_113 (sum)) ) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 ) ” 
  &&  “ (0 <= k) ” 
  &&  “ ((k + numlen ) <= outlen) ” 
  &&  “ ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) = 105) ” 
  &&  “ ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.undef_full (row_out + (k * sizeof(CHAR) ) ) numlen )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_8_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (out_l_2: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= t)) (PreH5 : (t < template_len_113)) (PreH6 : (0 <= i)) (PreH7 : (i < lst_size_pre)) (PreH8 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH9 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH10 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH11 : (all_ascii (decimal_digits_113 (sum)) )) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH16 : (0 <= k)) (PreH17 : ((k + numlen ) <= outlen)) (PreH18 : (ch = 105)) (PreH19 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH20 : (row_out <> 0)) (PreH21 : (out <> 0)) (PreH22 : (data <> 0)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows_2 )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l_2 )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (out_l: (@list Z)) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 (t + 1 ) (decimal_digits_113 (sum)) (k + numlen ) out_l ) ” 
  &&  “ (0 <= (k + numlen )) ” 
  &&  “ ((k + numlen ) <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out (k + numlen ) out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (out_l_2: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (retval: Z) (PreH1 : (0 <= numlen)) (PreH2 : (retval = (row_out + (k * sizeof(CHAR) ) ))) (PreH3 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH4 : (0 <= 1)) (PreH5 : (0 <= t)) (PreH6 : (t < template_len_113)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH11 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH12 : (all_ascii (decimal_digits_113 (sum)) )) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH17 : (0 <= k)) (PreH18 : ((k + numlen ) <= outlen)) (PreH19 : (ch = 105)) (PreH20 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH21 : (row_out <> 0)) (PreH22 : (out <> 0)) (PreH23 : (data <> 0)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (CharArray.full (row_out + (k * sizeof(CHAR) ) ) numlen (decimal_digits_113 (sum)) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full row_out k out_l_2 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z)))  (out_l: (@list Z)) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 (t + 1 ) (decimal_digits_113 (sum)) (k + numlen ) out_l ) ” 
  &&  “ (0 <= (k + numlen )) ” 
  &&  “ ((k + numlen ) <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (CharArray.full row_out (k + numlen ) out_l )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_8_2 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l_2: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (out_l: (@list Z)) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 (t + 1 ) (decimal_digits_113 (sum)) (k + 1 ) out_l ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) ” 
  &&  “ ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out (k + 1 ) out_l )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (tpl_v: Z) (k: Z) (out_l_2: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH5 : (t < 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l_2 )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (t + 1 )) ” 
  &&  “ ((t + 1 ) <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 (t + 1 ) (decimal_digits_113 (sum)) (k + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) (8))) ((@nil Z))))) ) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= (Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0)) ” 
  &&  “ ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (odd_count_rows_heap_113 output_ptrs_2 output_rows )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_entail_wit_9 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= numlen)) (PreH5 : (t >= 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (PtrArray.seg data 0 (i + 1 ) (app (output_ptrs_2) ((cons (row_out) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows (i + 1 ) output_rows ) ” 
  &&  “ ((Zlength (output_ptrs)) = (i + 1 )) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 (i + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
) \/
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= 1)) (PreH4 : (0 <= numlen)) (PreH5 : (t >= 56)) (PreH6 : (0 <= t)) (PreH7 : (t <= template_len_113)) (PreH8 : (0 <= i)) (PreH9 : (i < lst_size_pre)) (PreH10 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH11 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH12 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH16 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH17 : (0 <= k)) (PreH18 : (k <= outlen)) (PreH19 : (row_out <> 0)) (PreH20 : (out <> 0)) (PreH21 : (data <> 0)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (rows_well_formed_113 rows lst_size_pre )) (PreH25 : forall (p_3: Z) , (((0 <= p_3) /\ (p_3 < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p_3) (rows)))))))) + 1 ) < 32))) (PreH26 : forall (p_4: Z) , (((0 <= p_4) /\ (p_4 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_4) (rows)))))) < INT_MAX))) (PreH27 : (problem_113_pre_z rows )) (PreH28 : (odd_count_state_113 rows i output_rows_2 )) (PreH29 : (tpl_v = (LitMap (template_literal_113)))) ,
  (GlobalStrings_missing LitMap (cons (template_literal_113) ((cons (template_literal_113) ((@nil string))))) )
  **  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows (i + 1 ) output_rows ) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (row_out) ((@nil Z))))))) = (i + 1 )) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (odd_count_rows_heap_113 (app (output_ptrs_2) ((cons (row_out) ((@nil Z))))) output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
).

Definition odd_count_return_wit_1 := 
(
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (sum: Z) (n: Z) (data_2: Z) (out: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : (0 <= sum)) (PreH9 : (sum < INT_MAX)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (0 <= numlen)) (PreH13 : (numlen < 32)) (PreH14 : (0 <= outlen)) (PreH15 : (outlen < INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < INT_MAX)) (PreH18 : (0 <= t)) (PreH19 : (t <= template_len_113)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows_2 )) (PreH25 : ((Zlength (output_ptrs_2)) = i)) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data_2 0 i output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (scratch: Z)  (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) = lst_size_pre) ” 
  &&  “ ((Zlength (output_ptrs)) = lst_size_pre) ” 
  &&  “ (output_rows = (odd_count_rows_113 (rows))) ” 
  &&  “ (problem_113_spec_z rows output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (PtrArray.seg data 0 lst_size_pre output_ptrs )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full scratch 32 )
  **  (GlobalStrings LitMap )
) \/
(
forall (lst_size_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (tpl_v: Z) (t: Z) (k: Z) (outlen: Z) (numlen: Z) (ch: Z) (sum: Z) (n: Z) (data_2: Z) (out: Z) (i: Z) (PreH1 : (i >= lst_size_pre)) (PreH2 : (0 <= i)) (PreH3 : (i <= lst_size_pre)) (PreH4 : (out <> 0)) (PreH5 : (data_2 <> 0)) (PreH6 : (0 <= n)) (PreH7 : (n < INT_MAX)) (PreH8 : (0 <= sum)) (PreH9 : (sum < INT_MAX)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (0 <= numlen)) (PreH13 : (numlen < 32)) (PreH14 : (0 <= outlen)) (PreH15 : (outlen < INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < INT_MAX)) (PreH18 : (0 <= t)) (PreH19 : (t <= template_len_113)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows_2 )) (PreH25 : ((Zlength (output_ptrs_2)) = i)) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) ,
  (PtrArray.seg data_2 0 i output_ptrs_2 )
  **  (odd_count_rows_heap_113 output_ptrs_2 output_rows_2 )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  EX (scratch: Z)  (output_ptrs: (@list Z)) ,
  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ ((Zlength ((odd_count_rows_113 (rows)))) = lst_size_pre) ” 
  &&  “ ((Zlength (output_ptrs)) = lst_size_pre) ” 
  &&  “ (problem_113_spec_z rows (odd_count_rows_113 (rows)) ) ”
  &&  (PtrArray.seg data_2 0 lst_size_pre output_ptrs )
  **  (odd_count_rows_heap_113 output_ptrs (odd_count_rows_113 (rows)) )
  **  (CharArray.undef_full scratch 32 )
  **  (GlobalStrings LitMap )
).

Definition odd_count_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (PreH1 : (0 <= lst_size_pre)) (PreH2 : (lst_size_pre <= 100)) (PreH3 : (rows_well_formed_113 rows lst_size_pre )) (PreH4 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH5 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH6 : (problem_113_pre_z rows )) ,
  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= 100) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ”
  &&  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
.

Definition odd_count_partial_solve_wit_2_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre <= 100)) (PreH4 : (rows_well_formed_113 rows lst_size_pre )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH6 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH7 : (problem_113_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ”
.

Definition odd_count_partial_solve_wit_2_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= lst_size_pre)) (PreH3 : (lst_size_pre <= 100)) (PreH4 : (rows_well_formed_113 rows lst_size_pre )) (PreH5 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH6 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH7 : (problem_113_pre_z rows )) ,
  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= 100) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
  **  (GlobalStrings LitMap )
.

Definition odd_count_partial_solve_wit_2 := odd_count_partial_solve_wit_2_pure -> odd_count_partial_solve_wit_2_aux.

Definition odd_count_partial_solve_wit_3_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  ((( &( "numbuf" ) )) # Ptr  |->_)
  **  (store_stringLit (LitMap (("the number of odd elements in the string i of the input."%string))) ("the number of odd elements in the string i of the input."%string) )
  **  (GlobalStrings_missing LitMap (cons (("the number of odd elements in the string i of the input."%string)) ((@nil string))) )
  **  ((( &( "tpl" ) )) # Ptr  |-> ((LitMap (("the number of odd elements in the string i of the input."%string))) + (0 * sizeof(CHAR) ) ))
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "outlen" ) )) # Int  |-> 0)
  **  ((( &( "numlen" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (32 > 0) ” 
  &&  “ (32 < INT_MAX) ”
.

Definition odd_count_partial_solve_wit_3_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval <> 0)) (PreH3 : (0 <= lst_size_pre)) (PreH4 : (lst_size_pre <= 100)) (PreH5 : (rows_well_formed_113 rows lst_size_pre )) (PreH6 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH7 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH8 : (problem_113_pre_z rows )) ,
  (store_stringLit (LitMap (("the number of odd elements in the string i of the input."%string))) ("the number of odd elements in the string i of the input."%string) )
  **  (GlobalStrings_missing LitMap (cons (("the number of odd elements in the string i of the input."%string)) ((@nil string))) )
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
|--
  “ (32 > 0) ” 
  &&  “ (32 < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre <= 100) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ”
  &&  (GlobalStrings LitMap )
  **  (PtrArray.undef_full retval_2 lst_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (CharPtrArray2.full lst_pre lst_size_pre rows )
.

Definition odd_count_partial_solve_wit_3 := odd_count_partial_solve_wit_3_pure -> odd_count_partial_solve_wit_3_aux.

Definition odd_count_partial_solve_wit_4_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (0 <= numlen)) (PreH12 : (numlen < 32)) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < INT_MAX)) (PreH17 : (0 <= t)) (PreH18 : (t <= template_len_113)) (PreH19 : (rows_well_formed_113 rows lst_size_pre )) (PreH20 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH21 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH22 : (problem_113_pre_z rows )) (PreH23 : (odd_count_state_113 rows i output_rows )) (PreH24 : (tpl_v = (LitMap (template_literal_113)))) (PreH25 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH26 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH27 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) ) ” 
  &&  “ ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX) ”
.

Definition odd_count_partial_solve_wit_4_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (out: Z) (data: Z) (n: Z) (sum: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (0 <= n)) (PreH6 : (n < INT_MAX)) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (0 <= ch)) (PreH10 : (ch <= 127)) (PreH11 : (0 <= numlen)) (PreH12 : (numlen < 32)) (PreH13 : (0 <= outlen)) (PreH14 : (outlen < INT_MAX)) (PreH15 : (0 <= k)) (PreH16 : (k < INT_MAX)) (PreH17 : (0 <= t)) (PreH18 : (t <= template_len_113)) (PreH19 : (rows_well_formed_113 rows lst_size_pre )) (PreH20 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH21 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH22 : (problem_113_pre_z rows )) (PreH23 : (odd_count_state_113 rows i output_rows )) (PreH24 : (tpl_v = (LitMap (template_literal_113)))) (PreH25 : (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) )) (PreH26 : ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX)) (PreH27 : ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) ) ” 
  &&  “ ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ” 
  &&  “ (valid_string (row_payload_z_113 ((row_at_113 (i) (rows)))) ) ” 
  &&  “ ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) < INT_MAX) ” 
  &&  “ ((Zlength ((row_at_113 (i) (rows)))) = ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ”
  &&  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_4 := odd_count_partial_solve_wit_4_pure -> odd_count_partial_solve_wit_4_aux.

Definition odd_count_partial_solve_wit_5_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH4 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH5 : (0 <= sum)) (PreH6 : (sum < INT_MAX)) (PreH7 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (0 <= numlen)) (PreH13 : (numlen < 32)) (PreH14 : (0 <= outlen)) (PreH15 : (outlen < INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < INT_MAX)) (PreH18 : (0 <= t)) (PreH19 : (t <= template_len_113)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ”
.

Definition odd_count_partial_solve_wit_5_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (PreH1 : (0 <= i)) (PreH2 : (i < lst_size_pre)) (PreH3 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH4 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH5 : (0 <= sum)) (PreH6 : (sum < INT_MAX)) (PreH7 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= ch)) (PreH11 : (ch <= 127)) (PreH12 : (0 <= numlen)) (PreH13 : (numlen < 32)) (PreH14 : (0 <= outlen)) (PreH15 : (outlen < INT_MAX)) (PreH16 : (0 <= k)) (PreH17 : (k < INT_MAX)) (PreH18 : (0 <= t)) (PreH19 : (t <= template_len_113)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.undef_full numbuf 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharArray.undef_full numbuf 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_5 := odd_count_partial_solve_wit_5_pure -> odd_count_partial_solve_wit_5_aux.

Definition odd_count_partial_solve_wit_6_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "row_out" ) )) # Ptr  |->_)
  **  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numlen" ) )) # Int  |-> retval)
  **  ((( &( "outlen" ) )) # Int  |-> (56 + (4 * (retval - 1 ) ) ))
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (((56 + (4 * (retval - 1 ) ) ) + 1 ) > 0) ” 
  &&  “ (((56 + (4 * (retval - 1 ) ) ) + 1 ) < INT_MAX) ”
.

Definition odd_count_partial_solve_wit_6_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (tpl_v: Z) (i: Z) (n: Z) (sum: Z) (out: Z) (data: Z) (ch: Z) (numlen: Z) (outlen: Z) (k: Z) (t: Z) (numbuf: Z) (retval: Z) (PreH1 : (retval = (Zlength ((decimal_digits_113 (sum)))))) (PreH2 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (0 <= sum)) (PreH8 : (sum < INT_MAX)) (PreH9 : (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32)) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= ch)) (PreH13 : (ch <= 127)) (PreH14 : (0 <= numlen)) (PreH15 : (numlen < 32)) (PreH16 : (0 <= outlen)) (PreH17 : (outlen < INT_MAX)) (PreH18 : (0 <= k)) (PreH19 : (k < INT_MAX)) (PreH20 : (0 <= t)) (PreH21 : (t <= template_len_113)) (PreH22 : (rows_well_formed_113 rows lst_size_pre )) (PreH23 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH24 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH25 : (problem_113_pre_z rows )) (PreH26 : (odd_count_state_113 rows i output_rows )) (PreH27 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (((56 + (4 * (retval - 1 ) ) ) + 1 ) > 0) ” 
  &&  “ (((56 + (4 * (retval - 1 ) ) ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum < INT_MAX) ” 
  &&  “ (((Zlength ((decimal_digits_113 (sum)))) + 1 ) < 32) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < 32) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k < INT_MAX) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharArray.full numbuf retval (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (retval * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (retval + 1 ) 32 )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_6 := odd_count_partial_solve_wit_6_pure -> odd_count_partial_solve_wit_6_aux.

Definition odd_count_partial_solve_wit_7_pure := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (PreH1 : (0 <= t)) (PreH2 : (t < template_len_113)) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH8 : (all_ascii (decimal_digits_113 (sum)) )) (PreH9 : (0 <= outlen)) (PreH10 : (outlen < INT_MAX)) (PreH11 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH12 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH13 : (0 <= k)) (PreH14 : ((k + numlen ) <= outlen)) (PreH15 : (ch = 105)) (PreH16 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH17 : (row_out <> 0)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "numlen" ) )) # Int  |-> numlen)
  **  ((( &( "outlen" ) )) # Int  |-> outlen)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "tpl" ) )) # Ptr  |-> tpl_v)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "row_out" ) )) # Ptr  |-> row_out)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  ((( &( "numbuf" ) )) # Ptr  |-> numbuf)
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_full (row_out + (k * sizeof(CHAR) ) ) numlen )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (all_ascii (decimal_digits_113 (sum)) ) ” 
  &&  “ ((Zlength ((decimal_digits_113 (sum)))) = numlen) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < INT_MAX) ” 
  &&  “ (0 <= (Zlength ((decimal_digits_113 (sum))))) ”
.

Definition odd_count_partial_solve_wit_7_aux := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (row_ptr: Z) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (out_l: (@list Z)) (tpl_v: Z) (t: Z) (i: Z) (n: Z) (sum: Z) (numlen: Z) (outlen: Z) (k: Z) (ch: Z) (row_out: Z) (out: Z) (data: Z) (numbuf: Z) (PreH1 : (0 <= t)) (PreH2 : (t < template_len_113)) (PreH3 : (0 <= i)) (PreH4 : (i < lst_size_pre)) (PreH5 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH6 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH7 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH8 : (all_ascii (decimal_digits_113 (sum)) )) (PreH9 : (0 <= outlen)) (PreH10 : (outlen < INT_MAX)) (PreH11 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH12 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH13 : (0 <= k)) (PreH14 : ((k + numlen ) <= outlen)) (PreH15 : (ch = 105)) (PreH16 : ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105)) (PreH17 : (row_out <> 0)) (PreH18 : (out <> 0)) (PreH19 : (data <> 0)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_full (row_out + (k * sizeof(CHAR) ) ) numlen )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (all_ascii (decimal_digits_113 (sum)) ) ” 
  &&  “ ((Zlength ((decimal_digits_113 (sum)))) = numlen) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (numlen < INT_MAX) ” 
  &&  “ (0 <= (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (all_ascii (decimal_digits_113 (sum)) ) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l ) ” 
  &&  “ (0 <= k) ” 
  &&  “ ((k + numlen ) <= outlen) ” 
  &&  “ (ch = 105) ” 
  &&  “ ((Znth (t) ((StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 )))) (0)) = 105) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (CharArray.undef_full (row_out + (k * sizeof(CHAR) ) ) numlen )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out (k + numlen ) (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_7 := odd_count_partial_solve_wit_7_pure -> odd_count_partial_solve_wit_7_aux.

Definition odd_count_partial_solve_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105)) (PreH2 : (t < 56)) (PreH3 : (0 <= t)) (PreH4 : (t <= template_len_113)) (PreH5 : (0 <= i)) (PreH6 : (i < lst_size_pre)) (PreH7 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH8 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH9 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH10 : (0 <= outlen)) (PreH11 : (outlen < INT_MAX)) (PreH12 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH13 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH14 : (0 <= k)) (PreH15 : (k <= outlen)) (PreH16 : (row_out <> 0)) (PreH17 : (out <> 0)) (PreH18 : (data <> 0)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (rows_well_formed_113 rows lst_size_pre )) (PreH22 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH23 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH24 : (problem_113_pre_z rows )) (PreH25 : (odd_count_state_113 rows i output_rows )) (PreH26 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ ((Znth t (StringToList (template_literal_113) (((StringLength (template_literal_113)) + 1 ))) 0) <> 105) ” 
  &&  “ (t < 56) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (((row_out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharArray.undef_missing_i row_out k k (outlen + 1 ) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (t >= 56)) (PreH2 : (0 <= t)) (PreH3 : (t <= template_len_113)) (PreH4 : (0 <= i)) (PreH5 : (i < lst_size_pre)) (PreH6 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH7 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH8 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH9 : (0 <= outlen)) (PreH10 : (outlen < INT_MAX)) (PreH11 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH12 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH13 : (0 <= k)) (PreH14 : (k <= outlen)) (PreH15 : (row_out <> 0)) (PreH16 : (out <> 0)) (PreH17 : (data <> 0)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (rows_well_formed_113 rows lst_size_pre )) (PreH21 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH22 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH23 : (problem_113_pre_z rows )) (PreH24 : (odd_count_state_113 rows i output_rows )) (PreH25 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_113 ((row_at_113 (i) (rows)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (CharArray.undef_seg row_out k (outlen + 1 ) )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (t >= 56) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (((row_out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharArray.undef_missing_i row_out k k (outlen + 1 ) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (CharArray.full row_out k out_l )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Definition odd_count_partial_solve_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (rows: (@list (@list Z))) (numbuf: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (ch: Z) (data: Z) (out: Z) (row_out: Z) (row_ptr: Z) (tpl_v: Z) (k: Z) (out_l: (@list Z)) (outlen: Z) (numlen: Z) (sum: Z) (n: Z) (i: Z) (t: Z) (PreH1 : (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ))) (PreH2 : (0 <= 1)) (PreH3 : (0 <= numlen)) (PreH4 : (t >= 56)) (PreH5 : (0 <= t)) (PreH6 : (t <= template_len_113)) (PreH7 : (0 <= i)) (PreH8 : (i < lst_size_pre)) (PreH9 : (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))))) (PreH10 : (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows)))))) (PreH11 : (numlen = (Zlength ((decimal_digits_113 (sum)))))) (PreH12 : (0 <= outlen)) (PreH13 : (outlen < INT_MAX)) (PreH14 : (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 ))) (PreH15 : (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l )) (PreH16 : (0 <= k)) (PreH17 : (k <= outlen)) (PreH18 : (row_out <> 0)) (PreH19 : (out <> 0)) (PreH20 : (data <> 0)) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (rows_well_formed_113 rows lst_size_pre )) (PreH24 : forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32))) (PreH25 : forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX))) (PreH26 : (problem_113_pre_z rows )) (PreH27 : (odd_count_state_113 rows i output_rows )) (PreH28 : (tpl_v = (LitMap (template_literal_113)))) ,
  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (PtrArray.undef_seg data i lst_size_pre )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
|--
  “ (0 <= (k + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= numlen) ” 
  &&  “ (t >= 56) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t <= template_len_113) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (n = (string_length ((row_payload_z_113 ((row_at_113 (i) (rows))))))) ” 
  &&  “ (sum = (odd_digit_count_row_113 ((row_at_113 (i) (rows))))) ” 
  &&  “ (numlen = (Zlength ((decimal_digits_113 (sum))))) ” 
  &&  “ (0 <= outlen) ” 
  &&  “ (outlen < INT_MAX) ” 
  &&  “ (outlen = ((Zlength ((odd_count_row_113 ((row_at_113 (i) (rows)))))) - 1 )) ” 
  &&  “ (template_fill_state_113 t (decimal_digits_113 (sum)) k out_l ) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= outlen) ” 
  &&  “ (row_out <> 0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (rows_well_formed_113 rows lst_size_pre ) ” 
  &&  “ forall (p: Z) , (((0 <= p) /\ (p < lst_size_pre)) -> (((Zlength ((decimal_digits_113 ((odd_digit_count_row_113 ((row_at_113 (p) (rows)))))))) + 1 ) < 32)) ” 
  &&  “ forall (p_2: Z) , (((0 <= p_2) /\ (p_2 < lst_size_pre)) -> ((Zlength ((odd_count_row_113 ((row_at_113 (p_2) (rows)))))) < INT_MAX)) ” 
  &&  “ (problem_113_pre_z rows ) ” 
  &&  “ (odd_count_state_113 rows i output_rows ) ” 
  &&  “ (tpl_v = (LitMap (template_literal_113))) ”
  &&  (((data + (i * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (i + 1 ) lst_size_pre )
  **  (CharArray.full row_out (k + 1 ) (app (out_l) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg row_out (k + 1 ) (outlen + 1 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_113 ((row_at_113 (i) (rows)))))) + 1 ) (c_string ((row_payload_z_113 ((row_at_113 (i) (rows)))))) )
  **  (CharPtrArray2.missing_i lst_pre lst_size_pre i row_ptr rows )
  **  (((lst_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> lst_size_pre)
  **  (PtrArray.seg data 0 i output_ptrs )
  **  (odd_count_rows_heap_113 output_ptrs output_rows )
  **  (CharArray.full numbuf numlen (decimal_digits_113 (sum)) )
  **  (CharArray.full (numbuf + (numlen * sizeof(CHAR) ) ) 1 (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg numbuf (numlen + 1 ) 32 )
  **  (GlobalStrings_missing LitMap (cons (template_literal_113) ((@nil string))) )
  **  (store_stringLit tpl_v template_literal_113 )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_odd_count_safety_wit_1 : odd_count_safety_wit_1.
Axiom proof_of_odd_count_safety_wit_2 : odd_count_safety_wit_2.
Axiom proof_of_odd_count_safety_wit_3 : odd_count_safety_wit_3.
Axiom proof_of_odd_count_safety_wit_4 : odd_count_safety_wit_4.
Axiom proof_of_odd_count_safety_wit_5 : odd_count_safety_wit_5.
Axiom proof_of_odd_count_safety_wit_6 : odd_count_safety_wit_6.
Axiom proof_of_odd_count_safety_wit_7 : odd_count_safety_wit_7.
Axiom proof_of_odd_count_safety_wit_8 : odd_count_safety_wit_8.
Axiom proof_of_odd_count_safety_wit_9 : odd_count_safety_wit_9.
Axiom proof_of_odd_count_safety_wit_10 : odd_count_safety_wit_10.
Axiom proof_of_odd_count_safety_wit_11 : odd_count_safety_wit_11.
Axiom proof_of_odd_count_safety_wit_12 : odd_count_safety_wit_12.
Axiom proof_of_odd_count_safety_wit_13 : odd_count_safety_wit_13.
Axiom proof_of_odd_count_safety_wit_14 : odd_count_safety_wit_14.
Axiom proof_of_odd_count_safety_wit_15 : odd_count_safety_wit_15.
Axiom proof_of_odd_count_safety_wit_16 : odd_count_safety_wit_16.
Axiom proof_of_odd_count_safety_wit_17 : odd_count_safety_wit_17.
Axiom proof_of_odd_count_safety_wit_18 : odd_count_safety_wit_18.
Axiom proof_of_odd_count_safety_wit_19 : odd_count_safety_wit_19.
Axiom proof_of_odd_count_safety_wit_20 : odd_count_safety_wit_20.
Axiom proof_of_odd_count_safety_wit_21 : odd_count_safety_wit_21.
Axiom proof_of_odd_count_safety_wit_22 : odd_count_safety_wit_22.
Axiom proof_of_odd_count_safety_wit_23 : odd_count_safety_wit_23.
Axiom proof_of_odd_count_safety_wit_24 : odd_count_safety_wit_24.
Axiom proof_of_odd_count_safety_wit_25 : odd_count_safety_wit_25.
Axiom proof_of_odd_count_safety_wit_26 : odd_count_safety_wit_26.
Axiom proof_of_odd_count_safety_wit_27 : odd_count_safety_wit_27.
Axiom proof_of_odd_count_safety_wit_28 : odd_count_safety_wit_28.
Axiom proof_of_odd_count_safety_wit_29 : odd_count_safety_wit_29.
Axiom proof_of_odd_count_safety_wit_30 : odd_count_safety_wit_30.
Axiom proof_of_odd_count_safety_wit_31 : odd_count_safety_wit_31.
Axiom proof_of_odd_count_safety_wit_32 : odd_count_safety_wit_32.
Axiom proof_of_odd_count_safety_wit_33 : odd_count_safety_wit_33.
Axiom proof_of_odd_count_safety_wit_34 : odd_count_safety_wit_34.
Axiom proof_of_odd_count_safety_wit_35 : odd_count_safety_wit_35.
Axiom proof_of_odd_count_safety_wit_36 : odd_count_safety_wit_36.
Axiom proof_of_odd_count_safety_wit_37 : odd_count_safety_wit_37.
Axiom proof_of_odd_count_safety_wit_38 : odd_count_safety_wit_38.
Axiom proof_of_odd_count_safety_wit_39 : odd_count_safety_wit_39.
Axiom proof_of_odd_count_safety_wit_40 : odd_count_safety_wit_40.
Axiom proof_of_odd_count_safety_wit_41 : odd_count_safety_wit_41.
Axiom proof_of_odd_count_safety_wit_42 : odd_count_safety_wit_42.
Axiom proof_of_odd_count_safety_wit_43 : odd_count_safety_wit_43.
Axiom proof_of_odd_count_safety_wit_44 : odd_count_safety_wit_44.
Axiom proof_of_odd_count_safety_wit_45 : odd_count_safety_wit_45.
Axiom proof_of_odd_count_entail_wit_1 : odd_count_entail_wit_1.
Axiom proof_of_odd_count_entail_wit_2 : odd_count_entail_wit_2.
Axiom proof_of_odd_count_entail_wit_3 : odd_count_entail_wit_3.
Axiom proof_of_odd_count_entail_wit_4_1 : odd_count_entail_wit_4_1.
Axiom proof_of_odd_count_entail_wit_4_2 : odd_count_entail_wit_4_2.
Axiom proof_of_odd_count_entail_wit_4_3 : odd_count_entail_wit_4_3.
Axiom proof_of_odd_count_entail_wit_4_4 : odd_count_entail_wit_4_4.
Axiom proof_of_odd_count_entail_wit_5 : odd_count_entail_wit_5.
Axiom proof_of_odd_count_entail_wit_6 : odd_count_entail_wit_6.
Axiom proof_of_odd_count_entail_wit_7 : odd_count_entail_wit_7.
Axiom proof_of_odd_count_entail_wit_8_1 : odd_count_entail_wit_8_1.
Axiom proof_of_odd_count_entail_wit_8_2 : odd_count_entail_wit_8_2.
Axiom proof_of_odd_count_entail_wit_9 : odd_count_entail_wit_9.
Axiom proof_of_odd_count_return_wit_1 : odd_count_return_wit_1.
Axiom proof_of_odd_count_partial_solve_wit_1 : odd_count_partial_solve_wit_1.
Axiom proof_of_odd_count_partial_solve_wit_2_pure : odd_count_partial_solve_wit_2_pure.
Axiom proof_of_odd_count_partial_solve_wit_2 : odd_count_partial_solve_wit_2.
Axiom proof_of_odd_count_partial_solve_wit_3_pure : odd_count_partial_solve_wit_3_pure.
Axiom proof_of_odd_count_partial_solve_wit_3 : odd_count_partial_solve_wit_3.
Axiom proof_of_odd_count_partial_solve_wit_4_pure : odd_count_partial_solve_wit_4_pure.
Axiom proof_of_odd_count_partial_solve_wit_4 : odd_count_partial_solve_wit_4.
Axiom proof_of_odd_count_partial_solve_wit_5_pure : odd_count_partial_solve_wit_5_pure.
Axiom proof_of_odd_count_partial_solve_wit_5 : odd_count_partial_solve_wit_5.
Axiom proof_of_odd_count_partial_solve_wit_6_pure : odd_count_partial_solve_wit_6_pure.
Axiom proof_of_odd_count_partial_solve_wit_6 : odd_count_partial_solve_wit_6.
Axiom proof_of_odd_count_partial_solve_wit_7_pure : odd_count_partial_solve_wit_7_pure.
Axiom proof_of_odd_count_partial_solve_wit_7 : odd_count_partial_solve_wit_7.
Axiom proof_of_odd_count_partial_solve_wit_8 : odd_count_partial_solve_wit_8.
Axiom proof_of_odd_count_partial_solve_wit_9 : odd_count_partial_solve_wit_9.
Axiom proof_of_odd_count_partial_solve_wit_10 : odd_count_partial_solve_wit_10.

End VC_Correct.
