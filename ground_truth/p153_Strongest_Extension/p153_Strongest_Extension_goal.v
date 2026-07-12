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
Require Import p153_Strongest_Extension.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function extension_strength -----*)

Definition extension_strength_safety_wit_1 := 
forall (s_pre: Z) (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  ((( &( "strength" ) )) # Int  |->_)
  **  (store_string s_pre str )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extension_strength_safety_wit_2 := 
forall (s_pre: Z) (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |-> 0)
  **  (store_string s_pre str )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extension_strength_safety_wit_3 := 
forall (s_pre: Z) (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  ((( &( "chr" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "strength" ) )) # Int  |-> 0)
  **  (store_string s_pre str )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition extension_strength_safety_wit_4 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= j)) (PreH2 : (j < n)) (PreH3 : (n = (string_length (str)))) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : (valid_string str )) (PreH6 : (0 <= chr)) (PreH7 : (chr <= 127)) (PreH8 : (chr = (Znth (j) (str) (0)))) (PreH9 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition extension_strength_safety_wit_5 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr >= 65)) (PreH2 : (0 <= j)) (PreH3 : (j < n)) (PreH4 : (n = (string_length (str)))) (PreH5 : ((string_length (str)) <= 100)) (PreH6 : (valid_string str )) (PreH7 : (0 <= chr)) (PreH8 : (chr <= 127)) (PreH9 : (chr = (Znth (j) (str) (0)))) (PreH10 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition extension_strength_safety_wit_6 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (strength + 1 )) ”
) \/
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (strength + 1 )) ”
).

Definition extension_strength_safety_wit_6_split_goal_1 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength + 1 ) <= INT_MAX) ”
.

Definition extension_strength_safety_wit_6_split_goal_2 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((INT_MIN) <= (strength + 1 )) ”
.

Definition extension_strength_safety_wit_7 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_8 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength + 1 ))
  **  (store_string s_pre str )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition extension_strength_safety_wit_9 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr > 90)) (PreH2 : (chr >= 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition extension_strength_safety_wit_10 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 65)) (PreH2 : (0 <= j)) (PreH3 : (j < n)) (PreH4 : (n = (string_length (str)))) (PreH5 : ((string_length (str)) <= 100)) (PreH6 : (valid_string str )) (PreH7 : (0 <= chr)) (PreH8 : (chr <= 127)) (PreH9 : (chr = (Znth (j) (str) (0)))) (PreH10 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition extension_strength_safety_wit_11 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr >= 97)) (PreH2 : (chr <= 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength + 1 ))
  **  (store_string s_pre str )
|--
  “ False ”
.

Definition extension_strength_safety_wit_12 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr >= 97)) (PreH2 : (chr < 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ False ”
.

Definition extension_strength_safety_wit_13 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr >= 97)) (PreH2 : (chr > 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition extension_strength_safety_wit_14 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (strength - 1 )) ”
) \/
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (strength - 1 )) ”
).

Definition extension_strength_safety_wit_14_split_goal_1 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((strength - 1 ) <= INT_MAX) ”
.

Definition extension_strength_safety_wit_14_split_goal_2 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((INT_MIN) <= (strength - 1 )) ”
.

Definition extension_strength_safety_wit_15 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_16 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength - 1 ))
  **  (store_string s_pre str )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition extension_strength_safety_wit_17 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength - 1 ))
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_18 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr > 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition extension_strength_safety_wit_19 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr > 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_20 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr <= 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength + 1 ))
  **  (store_string s_pre str )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition extension_strength_safety_wit_21 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr <= 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> (strength + 1 ))
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_22 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr > 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition extension_strength_safety_wit_23 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr > 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_safety_wit_24 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr < 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition extension_strength_safety_wit_25 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr < 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "chr" ) )) # Int  |-> chr)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  (store_string s_pre str )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition extension_strength_entail_wit_1 := 
(
forall (s_pre: Z) (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  (store_string s_pre str )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (strength_scan_state_153 str 0 0 ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str 0 0 ) ” 
  &&  “ (0 <= retval) ”
  &&  emp
).

Definition extension_strength_entail_wit_1_split_goal_1 := 
forall (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str 0 0 ) ”
.

Definition extension_strength_entail_wit_1_split_goal_2 := 
forall (str: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str)))) (PreH2 : (0 <= ((string_length (str)) + 1 ))) (PreH3 : (valid_string str )) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : ((string_length (str)) < INT_MAX)) ,
  TT && emp 
|--
  “ (0 <= retval) ”
.

Definition extension_strength_entail_wit_2 := 
(
forall (s_pre: Z) (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (j < n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (n = (string_length (str)))) (PreH5 : ((string_length (str)) <= 100)) (PreH6 : (valid_string str )) (PreH7 : (strength_scan_state_153 str j strength )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) ,
  (store_string s_pre str )
|--
  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= (Znth j (c_string (str)) 0)) ” 
  &&  “ ((Znth j (c_string (str)) 0) <= 127) ” 
  &&  “ ((Znth j (c_string (str)) 0) = (Znth (j) (str) (0))) ” 
  &&  “ (strength_scan_state_153 str j strength ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ ((Znth j (c_string (str)) 0) = (Znth (j) (str) (0))) ” 
  &&  “ ((Znth j (c_string (str)) 0) <= 127) ” 
  &&  “ (0 <= (Znth j (c_string (str)) 0)) ”
  &&  emp
).

Definition extension_strength_entail_wit_2_split_goal_1 := 
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ ((Znth j (c_string (str)) 0) = (Znth (j) (str) (0))) ”
.

Definition extension_strength_entail_wit_2_split_goal_2 := 
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ ((Znth j (c_string (str)) 0) <= 127) ”
.

Definition extension_strength_entail_wit_2_split_goal_3 := 
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j < n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ (0 <= (Znth j (c_string (str)) 0)) ”
.

Definition extension_strength_entail_wit_3_1 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr < 65)) (PreH3 : (0 <= j)) (PreH4 : (j < n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) (PreH10 : (chr = (Znth (j) (str) (0)))) (PreH11 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ” 
  &&  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr < 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  emp
).

Definition extension_strength_entail_wit_3_1_split_goal_1 := 
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr < 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
.

Definition extension_strength_entail_wit_3_2 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr > 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ” 
  &&  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  emp
).

Definition extension_strength_entail_wit_3_2_split_goal_1 := 
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
.

Definition extension_strength_entail_wit_3_3 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr < 97)) (PreH2 : (chr <= 90)) (PreH3 : (chr >= 65)) (PreH4 : (0 <= j)) (PreH5 : (j < n)) (PreH6 : (n = (string_length (str)))) (PreH7 : ((string_length (str)) <= 100)) (PreH8 : (valid_string str )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) (PreH11 : (chr = (Znth (j) (str) (0)))) (PreH12 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ” 
  &&  “ (strength_scan_state_153 str (j + 1 ) (strength + 1 ) ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr <= 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) (strength + 1 ) ) ”
  &&  emp
).

Definition extension_strength_entail_wit_3_3_split_goal_1 := 
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr < 97)) (PreH3 : (chr <= 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) (strength + 1 ) ) ”
.

Definition extension_strength_entail_wit_3_4 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr > 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ” 
  &&  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr > 122)) (PreH3 : (chr >= 97)) (PreH4 : (chr > 90)) (PreH5 : (chr >= 65)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (n = (string_length (str)))) (PreH9 : ((string_length (str)) <= 100)) (PreH10 : (valid_string str )) (PreH11 : (0 <= chr)) (PreH12 : (chr <= 127)) (PreH13 : (chr = (Znth (j) (str) (0)))) (PreH14 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
  &&  emp
).

Definition extension_strength_entail_wit_3_4_split_goal_1 := 
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr > 122)) (PreH3 : (chr >= 97)) (PreH4 : (chr > 90)) (PreH5 : (chr >= 65)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (n = (string_length (str)))) (PreH9 : ((string_length (str)) <= 100)) (PreH10 : (valid_string str )) (PreH11 : (0 <= chr)) (PreH12 : (chr <= 127)) (PreH13 : (chr = (Znth (j) (str) (0)))) (PreH14 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) strength ) ”
.

Definition extension_strength_entail_wit_3_5 := 
(
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (chr <= 122)) (PreH2 : (chr >= 97)) (PreH3 : (chr > 90)) (PreH4 : (chr >= 65)) (PreH5 : (0 <= j)) (PreH6 : (j < n)) (PreH7 : (n = (string_length (str)))) (PreH8 : ((string_length (str)) <= 100)) (PreH9 : (valid_string str )) (PreH10 : (0 <= chr)) (PreH11 : (chr <= 127)) (PreH12 : (chr = (Znth (j) (str) (0)))) (PreH13 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ” 
  &&  “ (strength_scan_state_153 str (j + 1 ) (strength - 1 ) ) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr <= 122)) (PreH3 : (chr >= 97)) (PreH4 : (chr > 90)) (PreH5 : (chr >= 65)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (n = (string_length (str)))) (PreH9 : ((string_length (str)) <= 100)) (PreH10 : (valid_string str )) (PreH11 : (0 <= chr)) (PreH12 : (chr <= 127)) (PreH13 : (chr = (Znth (j) (str) (0)))) (PreH14 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) (strength - 1 ) ) ”
  &&  emp
).

Definition extension_strength_entail_wit_3_5_split_goal_1 := 
forall (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (chr <= 122)) (PreH3 : (chr >= 97)) (PreH4 : (chr > 90)) (PreH5 : (chr >= 65)) (PreH6 : (0 <= j)) (PreH7 : (j < n)) (PreH8 : (n = (string_length (str)))) (PreH9 : ((string_length (str)) <= 100)) (PreH10 : (valid_string str )) (PreH11 : (0 <= chr)) (PreH12 : (chr <= 127)) (PreH13 : (chr = (Znth (j) (str) (0)))) (PreH14 : (strength_scan_state_153 str j strength )) ,
  TT && emp 
|--
  “ (strength_scan_state_153 str (j + 1 ) (strength - 1 ) ) ”
.

Definition extension_strength_entail_wit_4 := 
forall (s_pre: Z) (str: (@list Z)) (j: Z) (n: Z) (chr: Z) (strength: Z) (PreH1 : (0 <= j)) (PreH2 : (j <= n)) (PreH3 : (n = (string_length (str)))) (PreH4 : ((string_length (str)) <= 100)) (PreH5 : (valid_string str )) (PreH6 : (0 <= chr)) (PreH7 : (chr <= 127)) (PreH8 : (strength_scan_state_153 str j strength )) ,
  (store_string s_pre str )
|--
  “ (0 <= j) ” 
  &&  “ (j <= n) ” 
  &&  “ (n = (string_length (str))) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ (valid_string str ) ” 
  &&  “ (strength_scan_state_153 str j strength ) ” 
  &&  “ (0 <= chr) ” 
  &&  “ (chr <= 127) ”
  &&  (store_string s_pre str )
.

Definition extension_strength_return_wit_1 := 
(
forall (s_pre: Z) (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (j >= n)) (PreH2 : (0 <= j)) (PreH3 : (j <= n)) (PreH4 : (n = (string_length (str)))) (PreH5 : ((string_length (str)) <= 100)) (PreH6 : (valid_string str )) (PreH7 : (strength_scan_state_153 str j strength )) (PreH8 : (0 <= chr)) (PreH9 : (chr <= 127)) ,
  (store_string s_pre str )
|--
  “ (strength = (extension_strength_z (str))) ”
  &&  (store_string s_pre str )
) \/
(
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j >= n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ (strength = (extension_strength_z (str))) ”
  &&  emp
).

Definition extension_strength_return_wit_1_split_goal_1 := 
forall (str: (@list Z)) (chr: Z) (strength: Z) (n: Z) (j: Z) (PreH1 : (0 <= ((string_length (str)) + 1 ))) (PreH2 : (j >= n)) (PreH3 : (0 <= j)) (PreH4 : (j <= n)) (PreH5 : (n = (string_length (str)))) (PreH6 : ((string_length (str)) <= 100)) (PreH7 : (valid_string str )) (PreH8 : (strength_scan_state_153 str j strength )) (PreH9 : (0 <= chr)) (PreH10 : (chr <= 127)) ,
  TT && emp 
|--
  “ (strength = (extension_strength_z (str))) ”
.

Definition extension_strength_partial_solve_wit_1_pure := 
forall (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : ((string_length (str)) <= 100)) (PreH3 : ((string_length (str)) < INT_MAX)) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
.

Definition extension_strength_partial_solve_wit_1_aux := 
forall (s_pre: Z) (str: (@list Z)) (PreH1 : (valid_string str )) (PreH2 : ((string_length (str)) <= 100)) (PreH3 : ((string_length (str)) < INT_MAX)) ,
  (store_string s_pre str )
|--
  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str)) + 1 )) ” 
  &&  “ (valid_string str ) ” 
  &&  “ ((string_length (str)) <= 100) ” 
  &&  “ ((string_length (str)) < INT_MAX) ”
  &&  (store_string s_pre str )
.

Definition extension_strength_partial_solve_wit_1 := extension_strength_partial_solve_wit_1_pure -> extension_strength_partial_solve_wit_1_aux.

(*----- Function Strongest_Extension -----*)

Definition Strongest_Extension_safety_wit_1 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "strongest" ) )) # Ptr  |->_)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_2 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |->_)
  **  ((( &( "strongest" ) )) # Ptr  |-> 0)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_3 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "strongest" ) )) # Ptr  |-> 0)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_4 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |->_)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "strongest" ) )) # Ptr  |-> 0)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_5 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |->_)
  **  ((( &( "strength" ) )) # Int  |-> 0)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "strongest" ) )) # Ptr  |-> 0)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_6 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best_idx" ) )) # Int  |-> 0)
  **  ((( &( "strength" ) )) # Int  |-> 0)
  **  ((( &( "max" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Ptr  |-> 0)
  **  ((( &( "strongest" ) )) # Ptr  |-> 0)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_7 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (strongest: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (strongest = 0)) (PreH4 : (cur = 0)) (PreH5 : (max = 0)) (PreH6 : (strength = 0)) (PreH7 : (best_idx = 0)) (PreH8 : (i = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> strongest)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_8 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (strongest: Z) (cur: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (max = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH4 : (cur = 0)) (PreH5 : (strength = 0)) (PreH6 : (best_idx = 0)) (PreH7 : (i = 0)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) ,
  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "strongest" ) )) # Ptr  |-> strongest)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Strongest_Extension_safety_wit_9 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strongest: Z) (cur: Z) (strength: Z) (max: Z) (best_idx: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx <= i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows (i + 1 ) best_idx max )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> strongest)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition Strongest_Extension_safety_wit_10 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strongest: Z) (cur: Z) (strength: Z) (max: Z) (best_idx: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx <= i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows (i + 1 ) best_idx max )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> strongest)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Strongest_Extension_safety_wit_11 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) (PreH8 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH11 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_12 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) (PreH8 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH11 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_13 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) (PreH8 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH11 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "n2" ) )) # Int  |->_)
  **  ((( &( "n1" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_safety_wit_14 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (out = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + retval ) + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n1 + retval ) + 2 )) ”
.

Definition Strongest_Extension_safety_wit_15 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (out = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + retval )) ”
.

Definition Strongest_Extension_safety_wit_16 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (out = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition Strongest_Extension_safety_wit_17 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (out <> 0)) (PreH7 : (valid_string class_l )) (PreH8 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out n1 class_l )
  **  (CharArray.undef_seg out n1 (n1 + 1 ) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition Strongest_Extension_safety_wit_18 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + 1 )) ”
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + 1 )) ”
).

Definition Strongest_Extension_safety_wit_18_split_goal_1 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + 1 ) <= INT_MAX) ”
.

Definition Strongest_Extension_safety_wit_18_split_goal_2 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((INT_MIN) <= (n1 + 1 )) ”
.

Definition Strongest_Extension_safety_wit_19 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Strongest_Extension_safety_wit_20 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + n2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n1 + n2 ) + 1 )) ”
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + n2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n1 + n2 ) + 1 )) ”
).

Definition Strongest_Extension_safety_wit_20_split_goal_1 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + n2 ) + 1 ) <= INT_MAX) ”
.

Definition Strongest_Extension_safety_wit_20_split_goal_2 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((INT_MIN) <= ((n1 + n2 ) + 1 )) ”
.

Definition Strongest_Extension_safety_wit_21 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + n2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + n2 )) ”
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + n2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n1 + n2 )) ”
).

Definition Strongest_Extension_safety_wit_21_split_goal_1 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((n1 + n2 ) <= INT_MAX) ”
.

Definition Strongest_Extension_safety_wit_21_split_goal_2 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ ((INT_MIN) <= (n1 + n2 )) ”
.

Definition Strongest_Extension_safety_wit_22 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition Strongest_Extension_safety_wit_23 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition Strongest_Extension_entail_wit_1 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) ,
  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
|--
  EX (row_ptr: Z) ,
  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (valid_string class_l )) (PreH6 : ((string_length (class_l)) <= 100)) (PreH7 : (rows_well_formed_153 rows extensions_size_pre )) (PreH8 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH9 : (problem_153_pre_z class_l rows )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) )
).

Definition Strongest_Extension_entail_wit_1_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (valid_string class_l )) (PreH6 : ((string_length (class_l)) <= 100)) (PreH7 : (rows_well_formed_153 rows extensions_size_pre )) (PreH8 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH9 : (problem_153_pre_z class_l rows )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_entail_wit_1_split_goal_2 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (valid_string class_l )) (PreH6 : ((string_length (class_l)) <= 100)) (PreH7 : (rows_well_formed_153 rows extensions_size_pre )) (PreH8 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH9 : (problem_153_pre_z class_l rows )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ”
.

Definition Strongest_Extension_entail_wit_1_split_goal_3 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (valid_string class_l )) (PreH6 : ((string_length (class_l)) <= 100)) (PreH7 : (rows_well_formed_153 rows extensions_size_pre )) (PreH8 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH9 : (problem_153_pre_z class_l rows )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
|--
  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ”
.

Definition Strongest_Extension_entail_wit_1_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth 0 rows __default__List_Z))))) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (valid_string class_l )) (PreH6 : ((string_length (class_l)) <= 100)) (PreH7 : (rows_well_formed_153 rows extensions_size_pre )) (PreH8 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH9 : (problem_153_pre_z class_l rows )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth 0 rows __default__List_Z))) (Znth 0 rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) )
.

Definition Strongest_Extension_entail_wit_2 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (strongest: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (strongest = 0)) (PreH4 : (cur = 0)) (PreH5 : (max = 0)) (PreH6 : (strength = 0)) (PreH7 : (best_idx = 0)) (PreH8 : (i = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (cur = 0) ” 
  &&  “ (max = 0) ” 
  &&  “ (strength = 0) ” 
  &&  “ (best_idx = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
.

Definition Strongest_Extension_entail_wit_3 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (cur = 0)) (PreH7 : (max = 0)) (PreH8 : (strength = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (i = 0)) (PreH11 : (valid_string class_l )) (PreH12 : ((string_length (class_l)) <= 100)) (PreH13 : (rows_well_formed_153 rows extensions_size_pre )) (PreH14 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH15 : (problem_153_pre_z class_l rows )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (retval = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z)))))))) ” 
  &&  “ (cur = 0) ” 
  &&  “ (strength = 0) ” 
  &&  “ (best_idx = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (cur = 0)) (PreH7 : (max = 0)) (PreH8 : (strength = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (i = 0)) (PreH11 : (valid_string class_l )) (PreH12 : ((string_length (class_l)) <= 100)) (PreH13 : (rows_well_formed_153 rows extensions_size_pre )) (PreH14 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH15 : (problem_153_pre_z class_l rows )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
).

Definition Strongest_Extension_entail_wit_3_split_goal_spatial := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (cur = 0)) (PreH7 : (max = 0)) (PreH8 : (strength = 0)) (PreH9 : (best_idx = 0)) (PreH10 : (i = 0)) (PreH11 : (valid_string class_l )) (PreH12 : ((string_length (class_l)) <= 100)) (PreH13 : (rows_well_formed_153 rows extensions_size_pre )) (PreH14 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH15 : (problem_153_pre_z class_l rows )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
.

Definition Strongest_Extension_entail_wit_4 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (cur: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (max = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH4 : (cur = 0)) (PreH5 : (strength = 0)) (PreH6 : (best_idx = 0)) (PreH7 : (i = 0)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < 1) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows 1 best_idx max ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (cur: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 < extensions_size_pre)) (PreH3 : (extensions_size_pre <= 100)) (PreH4 : (max = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH5 : (cur = 0)) (PreH6 : (strength = 0)) (PreH7 : (best_idx = 0)) (PreH8 : (i = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows 1 best_idx max ) ”
  &&  emp
).

Definition Strongest_Extension_entail_wit_4_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (cur: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 < extensions_size_pre)) (PreH3 : (extensions_size_pre <= 100)) (PreH4 : (max = (extension_strength_z ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))))) (PreH5 : (cur = 0)) (PreH6 : (strength = 0)) (PreH7 : (best_idx = 0)) (PreH8 : (i = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows 1 best_idx max ) ”
.

Definition Strongest_Extension_entail_wit_5 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (PreH1 : (i < extensions_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= extensions_size_pre)) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < i)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) (PreH13 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  EX (row_ptr: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows i best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) )
).

Definition Strongest_Extension_entail_wit_5_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_entail_wit_5_split_goal_2 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ”
.

Definition Strongest_Extension_entail_wit_5_split_goal_3 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ”
.

Definition Strongest_Extension_entail_wit_5_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth i rows __default__List_Z))))) (PreH3 : (i < extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth i rows __default__List_Z))) (Znth i rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) )
.

Definition Strongest_Extension_entail_wit_6 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (best_idx: Z) (max: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows i best_idx max )) (PreH13 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows i best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
.

Definition Strongest_Extension_entail_wit_7 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (best_idx: Z) (max: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (1 <= i)) (PreH5 : (i < extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (retval = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z)))))))) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows i best_idx max ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (best_idx: Z) (max: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (1 <= i)) (PreH5 : (i < extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
).

Definition Strongest_Extension_entail_wit_7_split_goal_spatial := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (best_idx: Z) (max: Z) (retval: Z) (PreH1 : (retval = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (1 <= i)) (PreH5 : (i < extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
.

Definition Strongest_Extension_entail_wit_8_1 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (strength <= max)) (PreH2 : (1 <= i)) (PreH3 : (i < extensions_size_pre)) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < i)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx <= i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows (i + 1 ) best_idx max ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (strength <= max)) (PreH3 : (1 <= i)) (PreH4 : (i < extensions_size_pre)) (PreH5 : (0 < extensions_size_pre)) (PreH6 : (extensions_size_pre <= 100)) (PreH7 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows (i + 1 ) best_idx max ) ”
  &&  emp
).

Definition Strongest_Extension_entail_wit_8_1_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (strength <= max)) (PreH3 : (1 <= i)) (PreH4 : (i < extensions_size_pre)) (PreH5 : (0 < extensions_size_pre)) (PreH6 : (extensions_size_pre <= 100)) (PreH7 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows (i + 1 ) best_idx max ) ”
.

Definition Strongest_Extension_entail_wit_8_2 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (strength > max)) (PreH2 : (1 <= i)) (PreH3 : (i < extensions_size_pre)) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < i)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows (i + 1 ) i strength ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (strength > max)) (PreH3 : (1 <= i)) (PreH4 : (i < extensions_size_pre)) (PreH5 : (0 < extensions_size_pre)) (PreH6 : (extensions_size_pre <= 100)) (PreH7 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows (i + 1 ) i strength ) ”
  &&  emp
).

Definition Strongest_Extension_entail_wit_8_2_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (strength > max)) (PreH3 : (1 <= i)) (PreH4 : (i < extensions_size_pre)) (PreH5 : (0 < extensions_size_pre)) (PreH6 : (extensions_size_pre <= 100)) (PreH7 : (strength = (extension_strength_z ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))))) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  TT && emp 
|--
  “ (best_prefix_state_153 rows (i + 1 ) i strength ) ”
.

Definition Strongest_Extension_entail_wit_9 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (i: Z) (max: Z) (best_idx: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx <= i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows (i + 1 ) best_idx max )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < (i + 1 )) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows (i + 1 ) best_idx max ) ”
  &&  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
.

Definition Strongest_Extension_entail_wit_10 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (PreH1 : (i >= extensions_size_pre)) (PreH2 : (1 <= i)) (PreH3 : (i <= extensions_size_pre)) (PreH4 : (0 < extensions_size_pre)) (PreH5 : (extensions_size_pre <= 100)) (PreH6 : (0 <= best_idx)) (PreH7 : (best_idx < i)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) (PreH13 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string class_name_pre class_l )
|--
  EX (row_ptr: Z) ,
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
).

Definition Strongest_Extension_entail_wit_10_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_entail_wit_10_split_goal_2 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ”
.

Definition Strongest_Extension_entail_wit_10_split_goal_3 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ”
.

Definition Strongest_Extension_entail_wit_10_split_goal_4 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
.

Definition Strongest_Extension_entail_wit_10_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (max: Z) (best_idx: Z) (i: Z) (row_ptr_2: Z)  __default__List_Z (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= (Zlength ((Znth best_idx rows __default__List_Z))))) (PreH3 : (i >= extensions_size_pre)) (PreH4 : (1 <= i)) (PreH5 : (i <= extensions_size_pre)) (PreH6 : (0 < extensions_size_pre)) (PreH7 : (extensions_size_pre <= 100)) (PreH8 : (0 <= best_idx)) (PreH9 : (best_idx < i)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows i best_idx max )) ,
  (CharArray.full row_ptr_2 (Zlength ((Znth best_idx rows __default__List_Z))) (Znth best_idx rows __default__List_Z) )
|--
  (CharArray.full row_ptr_2 ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
.

Definition Strongest_Extension_entail_wit_11 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (valid_string class_l )) (PreH4 : ((string_length (class_l)) <= 100)) (PreH5 : (rows_well_formed_153 rows extensions_size_pre )) (PreH6 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH7 : (problem_153_pre_z class_l rows )) (PreH8 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH11 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
.

Definition Strongest_Extension_entail_wit_12 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (out: Z) (max: Z) (n1: Z) (n2: Z) (retval: Z) (PreH1 : (retval = (string_length (class_l)))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (out = 0)) (PreH7 : (n1 = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string class_name_pre class_l )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (retval = (string_length (class_l))) ” 
  &&  “ (out = 0) ” 
  &&  “ (n2 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
.

Definition Strongest_Extension_entail_wit_13 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (retval = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (((n1 + retval ) + 2 ) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (all_ascii class_l ) ” 
  &&  “ ((Zlength (class_l)) = n1) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full retval_2 n1 )
  **  (CharArray.undef_seg retval_2 n1 ((n1 + retval ) + 2 ) )
) \/
(
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  “ (0 <= n1) ” 
  &&  “ ((Zlength (class_l)) = n1) ” 
  &&  “ (all_ascii class_l ) ” 
  &&  “ (retval = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ”
  &&  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full retval_2 n1 )
  **  (CharArray.undef_seg retval_2 n1 ((n1 + retval ) + 2 ) )
).

Definition Strongest_Extension_entail_wit_13_split_goal_1 := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  “ (0 <= n1) ”
.

Definition Strongest_Extension_entail_wit_13_split_goal_2 := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  “ ((Zlength (class_l)) = n1) ”
.

Definition Strongest_Extension_entail_wit_13_split_goal_3 := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  “ (all_ascii class_l ) ”
.

Definition Strongest_Extension_entail_wit_13_split_goal_4 := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  “ (retval = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ”
.

Definition Strongest_Extension_entail_wit_13_split_goal_spatial := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH3 : (0 <= ((string_length (class_l)) + 1 ))) (PreH4 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (out = 0)) (PreH9 : (n2 = 0)) (PreH10 : (valid_string class_l )) (PreH11 : ((string_length (class_l)) <= 100)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH16 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH18 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.undef_full retval_2 ((n1 + retval ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
|--
  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full retval_2 n1 )
  **  (CharArray.undef_seg retval_2 n1 ((n1 + retval ) + 2 ) )
.

Definition Strongest_Extension_entail_wit_14 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = out)) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= best_idx)) (PreH4 : (best_idx < extensions_size_pre)) (PreH5 : (n1 = (string_length (class_l)))) (PreH6 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH7 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (valid_string class_l )) (PreH10 : (all_ascii class_l )) (PreH11 : ((Zlength (class_l)) = n1)) (PreH12 : (0 <= n1)) (PreH13 : (n1 < INT_MAX)) (PreH14 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out n1 class_l )
  **  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out n1 class_l )
  **  (CharArray.undef_seg out n1 (n1 + 1 ) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
) \/
(
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = out)) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= best_idx)) (PreH4 : (best_idx < extensions_size_pre)) (PreH5 : (n1 = (string_length (class_l)))) (PreH6 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH7 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (valid_string class_l )) (PreH10 : (all_ascii class_l )) (PreH11 : ((Zlength (class_l)) = n1)) (PreH12 : (0 <= n1)) (PreH13 : (n1 < INT_MAX)) (PreH14 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= n2) ”
  &&  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.undef_seg out n1 (n1 + 1 ) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
).

Definition Strongest_Extension_entail_wit_14_split_goal_1 := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = out)) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= best_idx)) (PreH4 : (best_idx < extensions_size_pre)) (PreH5 : (n1 = (string_length (class_l)))) (PreH6 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH7 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (valid_string class_l )) (PreH10 : (all_ascii class_l )) (PreH11 : ((Zlength (class_l)) = n1)) (PreH12 : (0 <= n1)) (PreH13 : (n1 < INT_MAX)) (PreH14 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= n2) ”
.

Definition Strongest_Extension_entail_wit_14_split_goal_spatial := 
forall (extensions_size_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = out)) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= best_idx)) (PreH4 : (best_idx < extensions_size_pre)) (PreH5 : (n1 = (string_length (class_l)))) (PreH6 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH7 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH8 : (out <> 0)) (PreH9 : (valid_string class_l )) (PreH10 : (all_ascii class_l )) (PreH11 : ((Zlength (class_l)) = n1)) (PreH12 : (0 <= n1)) (PreH13 : (n1 < INT_MAX)) (PreH14 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
|--
  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.undef_seg out n1 (n1 + 1 ) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
.

Definition Strongest_Extension_entail_wit_15 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) (n1 + 1 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ” 
  &&  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (n2 < INT_MAX) ”
  &&  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
).

Definition Strongest_Extension_entail_wit_15_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ”
.

Definition Strongest_Extension_entail_wit_15_split_goal_2 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ”
.

Definition Strongest_Extension_entail_wit_15_split_goal_3 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (n2 < INT_MAX) ”
.

Definition Strongest_Extension_entail_wit_15_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= n1)) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
.

Definition Strongest_Extension_entail_wit_16 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = (out + ((n1 + 1 ) * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= (n1 + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (n2 < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (valid_string class_l )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH14 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = (out + ((n1 + 1 ) * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= (n1 + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (n2 < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (valid_string class_l )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH14 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
).

Definition Strongest_Extension_entail_wit_16_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (retval: Z) (PreH1 : (retval = (out + ((n1 + 1 ) * sizeof(CHAR) ) ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= (n1 + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (0 <= n2)) (PreH9 : (n2 < INT_MAX)) (PreH10 : (out <> 0)) (PreH11 : (valid_string class_l )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH14 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH15 : (rows_well_formed_153 rows extensions_size_pre )) (PreH16 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH17 : (problem_153_pre_z class_l rows )) (PreH18 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
|--
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
.

Definition Strongest_Extension_entail_wit_17 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= ((string_length (class_l)) + 1 ))) (PreH2 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH3 : (0 <= ((n1 + n2 ) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH8 : (out <> 0)) (PreH9 : (valid_string class_l )) (PreH10 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out (((n1 + n2 ) + 1 ) + 1 ) (app ((app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out (((n1 + n2 ) + 1 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (out_l: (@list Z)) ,
  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (out_l = (output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (problem_153_spec_z class_l rows out_l ) ”
  &&  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (store_string out out_l )
) \/
(
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= (((n1 + n2 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= ((n1 + n2 ) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out (((n1 + n2 ) + 1 ) + 1 ) (app ((app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
|--
  “ (problem_153_spec_z class_l rows (output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) ) ”
  &&  (CharArray.full out ((string_length ((output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) + 1 ) (c_string ((output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) )
).

Definition Strongest_Extension_entail_wit_17_split_goal_1 := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= (((n1 + n2 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= ((n1 + n2 ) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out (((n1 + n2 ) + 1 ) + 1 ) (app ((app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
|--
  “ (problem_153_spec_z class_l rows (output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) ) ”
.

Definition Strongest_Extension_entail_wit_17_split_goal_spatial := 
forall (extensions_size_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= (((n1 + n2 ) + 1 ) + 1 ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= ((n1 + n2 ) + 1 ))) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < extensions_size_pre)) (PreH7 : (n1 = (string_length (class_l)))) (PreH8 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH9 : (out <> 0)) (PreH10 : (valid_string class_l )) (PreH11 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharArray.full out (((n1 + n2 ) + 1 ) + 1 ) (app ((app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ((cons (0) ((@nil Z))))) )
|--
  (CharArray.full out ((string_length ((output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) + 1 ) (c_string ((output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) )
.

Definition Strongest_Extension_return_wit_1 := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (out_l_2: (@list Z)) (best_idx: Z) (out: Z) (n1: Z) (n2: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (out_l_2 = (output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH4 : (out <> 0)) (PreH5 : (n1 = (string_length (class_l)))) (PreH6 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH7 : (0 <= best_idx)) (PreH8 : (best_idx < extensions_size_pre)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH12 : (problem_153_spec_z class_l rows out_l_2 )) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (store_string out out_l_2 )
|--
  EX (out_l: (@list Z)) ,
  “ (problem_153_spec_z class_l rows out_l ) ”
  &&  (store_string class_name_pre class_l )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
  **  (store_string out out_l )
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (out_l_2: (@list Z)) (best_idx: Z) (out: Z) (n1: Z) (n2: Z) (max: Z) (PreH1 : (0 <= ((string_length (out_l_2)) + 1 ))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (out_l_2 = (output_payload_153 (class_l) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH7 : (out <> 0)) (PreH8 : (n1 = (string_length (class_l)))) (PreH9 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH10 : (0 <= best_idx)) (PreH11 : (best_idx < extensions_size_pre)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (problem_153_spec_z class_l rows out_l_2 )) ,
  (CharArray.full out ((string_length (out_l_2)) + 1 ) (c_string (out_l_2)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  EX (out_l: (@list Z)) ,
  “ (problem_153_spec_z class_l rows out_l ) ”
  &&  (CharArray.full out ((string_length (out_l)) + 1 ) (c_string (out_l)) )
  **  (CharPtrArray2.full extensions_pre extensions_size_pre rows )
).

Definition Strongest_Extension_partial_solve_wit_1_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (cur = 0)) (PreH4 : (max = 0)) (PreH5 : (strength = 0)) (PreH6 : (best_idx = 0)) (PreH7 : (i = 0)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) (PreH13 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_1_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (cur: Z) (max: Z) (strength: Z) (best_idx: Z) (i: Z) (PreH1 : (0 < extensions_size_pre)) (PreH2 : (extensions_size_pre <= 100)) (PreH3 : (cur = 0)) (PreH4 : (max = 0)) (PreH5 : (strength = 0)) (PreH6 : (best_idx = 0)) (PreH7 : (i = 0)) (PreH8 : (valid_string class_l )) (PreH9 : ((string_length (class_l)) <= 100)) (PreH10 : (rows_well_formed_153 rows extensions_size_pre )) (PreH11 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH12 : (problem_153_pre_z class_l rows )) (PreH13 : (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100)) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (cur = 0) ” 
  &&  “ (max = 0) ” 
  &&  “ (strength = 0) ” 
  &&  “ (best_idx = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_153 ((Znth (0) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre 0 row_ptr rows )
  **  (((extensions_pre + (0 * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition Strongest_Extension_partial_solve_wit_1 := Strongest_Extension_partial_solve_wit_1_pure -> Strongest_Extension_partial_solve_wit_1_aux.

Definition Strongest_Extension_partial_solve_wit_2_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (strongest: Z) (strength: Z) (best_idx: Z) (max: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows i best_idx max )) (PreH13 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "cur" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "strongest" ) )) # Ptr  |-> strongest)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_2_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (i: Z) (best_idx: Z) (max: Z) (PreH1 : (1 <= i)) (PreH2 : (i < extensions_size_pre)) (PreH3 : (0 < extensions_size_pre)) (PreH4 : (extensions_size_pre <= 100)) (PreH5 : (0 <= best_idx)) (PreH6 : (best_idx < i)) (PreH7 : (valid_string class_l )) (PreH8 : ((string_length (class_l)) <= 100)) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows i best_idx max )) (PreH13 : (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100)) (PreH15 : ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i < extensions_size_pre) ” 
  &&  “ (0 < extensions_size_pre) ” 
  &&  “ (extensions_size_pre <= 100) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < i) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows i best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_153 ((Znth (i) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre i row_ptr rows )
  **  (((extensions_pre + (i * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition Strongest_Extension_partial_solve_wit_2 := Strongest_Extension_partial_solve_wit_2_pure -> Strongest_Extension_partial_solve_wit_2_aux.

Definition Strongest_Extension_partial_solve_wit_3_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n1: Z) (n2: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (out = 0)) (PreH4 : (n1 = 0)) (PreH5 : (n2 = 0)) (PreH6 : (valid_string class_l )) (PreH7 : ((string_length (class_l)) <= 100)) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_3_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (out: Z) (max: Z) (n1: Z) (n2: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (out = 0)) (PreH4 : (n1 = 0)) (PreH5 : (n2 = 0)) (PreH6 : (valid_string class_l )) (PreH7 : ((string_length (class_l)) <= 100)) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (out = 0) ” 
  &&  “ (n1 = 0) ” 
  &&  “ (n2 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string class_name_pre class_l )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition Strongest_Extension_partial_solve_wit_3 := Strongest_Extension_partial_solve_wit_3_pure -> Strongest_Extension_partial_solve_wit_3_aux.

Definition Strongest_Extension_partial_solve_wit_4_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (out = 0)) (PreH5 : (n2 = 0)) (PreH6 : (valid_string class_l )) (PreH7 : ((string_length (class_l)) <= 100)) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_4_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (out = 0)) (PreH5 : (n2 = 0)) (PreH6 : (valid_string class_l )) (PreH7 : ((string_length (class_l)) <= 100)) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH14 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
|--
  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (out = 0) ” 
  &&  “ (n2 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition Strongest_Extension_partial_solve_wit_4 := Strongest_Extension_partial_solve_wit_4_pure -> Strongest_Extension_partial_solve_wit_4_aux.

Definition Strongest_Extension_partial_solve_wit_5_pure := 
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (out = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + retval ) + 2 ) < INT_MAX) ” 
  &&  “ (((n1 + retval ) + 2 ) > 0) ”
) \/
(
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (i_addr_v <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (max <= INT_MAX)) (PreH4 : (strength <= INT_MAX)) (PreH5 : (extensions_size_pre <= INT_MAX)) (PreH6 : (n1 <= INT_MAX)) (PreH7 : (best_idx <= INT_MAX)) (PreH8 : (i_addr_v >= INT_MIN)) (PreH9 : (retval >= INT_MIN)) (PreH10 : (max >= INT_MIN)) (PreH11 : (strength >= INT_MIN)) (PreH12 : (extensions_size_pre >= INT_MIN)) (PreH13 : (n1 >= INT_MIN)) (PreH14 : (best_idx >= INT_MIN)) (PreH15 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH16 : (0 <= ((string_length (class_l)) + 1 ))) (PreH17 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH18 : (0 <= best_idx)) (PreH19 : (best_idx < extensions_size_pre)) (PreH20 : (n1 = (string_length (class_l)))) (PreH21 : (out = 0)) (PreH22 : (n2 = 0)) (PreH23 : (valid_string class_l )) (PreH24 : ((string_length (class_l)) <= 100)) (PreH25 : (rows_well_formed_153 rows extensions_size_pre )) (PreH26 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH27 : (problem_153_pre_z class_l rows )) (PreH28 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH29 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH30 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH31 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + retval ) + 2 ) > 0) ”
).

Definition Strongest_Extension_partial_solve_wit_5_pure_split_goal_1 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (cur: Z) (out: Z) (strength: Z) (max: Z) (n2: Z) (i_addr_v: Z) (retval: Z) (PreH1 : (i_addr_v <= INT_MAX)) (PreH2 : (retval <= INT_MAX)) (PreH3 : (max <= INT_MAX)) (PreH4 : (strength <= INT_MAX)) (PreH5 : (extensions_size_pre <= INT_MAX)) (PreH6 : (n1 <= INT_MAX)) (PreH7 : (best_idx <= INT_MAX)) (PreH8 : (i_addr_v >= INT_MIN)) (PreH9 : (retval >= INT_MIN)) (PreH10 : (max >= INT_MIN)) (PreH11 : (strength >= INT_MIN)) (PreH12 : (extensions_size_pre >= INT_MIN)) (PreH13 : (n1 >= INT_MIN)) (PreH14 : (best_idx >= INT_MIN)) (PreH15 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH16 : (0 <= ((string_length (class_l)) + 1 ))) (PreH17 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH18 : (0 <= best_idx)) (PreH19 : (best_idx < extensions_size_pre)) (PreH20 : (n1 = (string_length (class_l)))) (PreH21 : (out = 0)) (PreH22 : (n2 = 0)) (PreH23 : (valid_string class_l )) (PreH24 : ((string_length (class_l)) <= 100)) (PreH25 : (rows_well_formed_153 rows extensions_size_pre )) (PreH26 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH27 : (problem_153_pre_z class_l rows )) (PreH28 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH29 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH30 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH31 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (((n1 + retval ) + 2 ) > 0) ”
.

Definition Strongest_Extension_partial_solve_wit_5_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (out: Z) (max: Z) (n2: Z) (retval: Z) (PreH1 : (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))))) (PreH2 : (0 <= ((string_length (class_l)) + 1 ))) (PreH3 : (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ))) (PreH4 : (0 <= best_idx)) (PreH5 : (best_idx < extensions_size_pre)) (PreH6 : (n1 = (string_length (class_l)))) (PreH7 : (out = 0)) (PreH8 : (n2 = 0)) (PreH9 : (valid_string class_l )) (PreH10 : ((string_length (class_l)) <= 100)) (PreH11 : (rows_well_formed_153 rows extensions_size_pre )) (PreH12 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH13 : (problem_153_pre_z class_l rows )) (PreH14 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) (PreH15 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH16 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100)) (PreH17 : ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX)) ,
  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
|--
  “ (((n1 + retval ) + 2 ) < INT_MAX) ” 
  &&  “ (((n1 + retval ) + 2 ) > 0) ” 
  &&  “ (retval = (string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))))) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (out = 0) ” 
  &&  “ (n2 = 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ ((string_length (class_l)) <= 100) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) <= 100) ” 
  &&  “ ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) < INT_MAX) ”
  &&  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
.

Definition Strongest_Extension_partial_solve_wit_5 := Strongest_Extension_partial_solve_wit_5_pure -> Strongest_Extension_partial_solve_wit_5_aux.

Definition Strongest_Extension_partial_solve_wit_6_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (valid_string class_l )) (PreH8 : (all_ascii class_l )) (PreH9 : ((Zlength (class_l)) = n1)) (PreH10 : (0 <= n1)) (PreH11 : (n1 < INT_MAX)) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : (rows_well_formed_153 rows extensions_size_pre )) (PreH14 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH15 : (problem_153_pre_z class_l rows )) (PreH16 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full out n1 )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (all_ascii class_l ) ” 
  &&  “ ((Zlength (class_l)) = n1) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_6_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (((n1 + n2 ) + 2 ) < INT_MAX)) (PreH6 : (out <> 0)) (PreH7 : (valid_string class_l )) (PreH8 : (all_ascii class_l )) (PreH9 : ((Zlength (class_l)) = n1)) (PreH10 : (0 <= n1)) (PreH11 : (n1 < INT_MAX)) (PreH12 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH13 : (rows_well_formed_153 rows extensions_size_pre )) (PreH14 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH15 : (problem_153_pre_z class_l rows )) (PreH16 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_full out n1 )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
|--
  “ (all_ascii class_l ) ” 
  &&  “ ((Zlength (class_l)) = n1) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (((n1 + n2 ) + 2 ) < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (all_ascii class_l ) ” 
  &&  “ ((Zlength (class_l)) = n1) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharArray.undef_full out n1 )
  **  (CharArray.full class_name_pre n1 class_l )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg class_name_pre n1 (n1 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.undef_seg out n1 ((n1 + n2 ) + 2 ) )
.

Definition Strongest_Extension_partial_solve_wit_6 := Strongest_Extension_partial_solve_wit_6_pure -> Strongest_Extension_partial_solve_wit_6_aux.

Definition Strongest_Extension_partial_solve_wit_7 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (out <> 0)) (PreH7 : (valid_string class_l )) (PreH8 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH9 : (rows_well_formed_153 rows extensions_size_pre )) (PreH10 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH11 : (problem_153_pre_z class_l rows )) (PreH12 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out n1 class_l )
  **  (CharArray.undef_seg out n1 (n1 + 1 ) )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (((out + (n1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_missing_i out n1 n1 (n1 + 1 ) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full out n1 class_l )
  **  (CharArray.undef_seg out (n1 + 1 ) ((n1 + n2 ) + 2 ) )
.

Definition Strongest_Extension_partial_solve_wit_8_pure := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (cur: Z) (strength: Z) (max: Z) (i_addr_v: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  ((( &( "best_idx" ) )) # Int  |-> best_idx)
  **  ((( &( "n1" ) )) # Int  |-> n1)
  **  ((( &( "n2" ) )) # Int  |-> n2)
  **  ((( &( "extensions_size" ) )) # Int  |-> extensions_size_pre)
  **  ((( &( "extensions" ) )) # Ptr  |-> extensions_pre)
  **  ((( &( "class_name" ) )) # Ptr  |-> class_name_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "strongest" ) )) # Ptr  |-> row_ptr)
  **  ((( &( "cur" ) )) # Ptr  |-> cur)
  **  ((( &( "strength" ) )) # Int  |-> strength)
  **  ((( &( "max" ) )) # Int  |-> max)
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  ((( &( "i" ) )) # Int  |-> i_addr_v)
|--
  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 < INT_MAX) ”
.

Definition Strongest_Extension_partial_solve_wit_8_aux := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (0 <= n2)) (PreH6 : (n2 < INT_MAX)) (PreH7 : (out <> 0)) (PreH8 : (valid_string class_l )) (PreH9 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH10 : (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH11 : ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2)) (PreH12 : (rows_well_formed_153 rows extensions_size_pre )) (PreH13 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH14 : (problem_153_pre_z class_l rows )) (PreH15 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (0 <= n2) ” 
  &&  “ (n2 < INT_MAX) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (all_ascii (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ ((Zlength ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) = n2) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (CharArray.undef_full (out + ((n1 + 1 ) * sizeof(CHAR) ) ) n2 )
  **  (CharArray.full row_ptr n2 (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.seg row_ptr n2 (n2 + 1 ) (cons (0) ((@nil Z))) )
  **  (CharArray.full out (n1 + 1 ) (app (class_l) ((cons (46) ((@nil Z))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
.

Definition Strongest_Extension_partial_solve_wit_8 := Strongest_Extension_partial_solve_wit_8_pure -> Strongest_Extension_partial_solve_wit_8_aux.

Definition Strongest_Extension_partial_solve_wit_9 := 
forall (extensions_size_pre: Z) (extensions_pre: Z) (class_name_pre: Z) (rows: (@list (@list Z))) (class_l: (@list Z)) (row_ptr: Z) (best_idx: Z) (n1: Z) (n2: Z) (out: Z) (max: Z) (PreH1 : (0 <= best_idx)) (PreH2 : (best_idx < extensions_size_pre)) (PreH3 : (n1 = (string_length (class_l)))) (PreH4 : (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) (PreH5 : (out <> 0)) (PreH6 : (valid_string class_l )) (PreH7 : (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )) (PreH8 : (rows_well_formed_153 rows extensions_size_pre )) (PreH9 : (output_len_safe_153 class_l rows extensions_size_pre )) (PreH10 : (problem_153_pre_z class_l rows )) (PreH11 : (best_prefix_state_153 rows extensions_size_pre best_idx max )) ,
  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (store_string row_ptr (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) )
  **  (store_string class_name_pre class_l )
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_seg out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
|--
  “ (0 <= ((string_length (class_l)) + 1 )) ” 
  &&  “ (0 <= ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 )) ” 
  &&  “ (0 <= ((n1 + n2 ) + 1 )) ” 
  &&  “ (0 <= best_idx) ” 
  &&  “ (best_idx < extensions_size_pre) ” 
  &&  “ (n1 = (string_length (class_l))) ” 
  &&  “ (n2 = (row_len_z_153 ((Znth (best_idx) (rows) ((@nil Z)))))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (valid_string class_l ) ” 
  &&  “ (valid_string (row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))) ) ” 
  &&  “ (rows_well_formed_153 rows extensions_size_pre ) ” 
  &&  “ (output_len_safe_153 class_l rows extensions_size_pre ) ” 
  &&  “ (problem_153_pre_z class_l rows ) ” 
  &&  “ (best_prefix_state_153 rows extensions_size_pre best_idx max ) ”
  &&  (((out + (((n1 + n2 ) + 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full class_name_pre ((string_length (class_l)) + 1 ) (c_string (class_l)) )
  **  (CharArray.full row_ptr ((string_length ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) + 1 ) (c_string ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
  **  (CharArray.undef_missing_i out ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 1 ) ((n1 + n2 ) + 2 ) )
  **  (CharPtrArray2.missing_i extensions_pre extensions_size_pre best_idx row_ptr rows )
  **  (((extensions_pre + (best_idx * sizeof(PTR) ) )) # Ptr  |-> row_ptr)
  **  (CharArray.full out ((n1 + n2 ) + 1 ) (app ((app (class_l) ((cons (46) ((@nil Z)))))) ((row_payload_z_153 ((Znth (best_idx) (rows) ((@nil Z))))))) )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_extension_strength_safety_wit_1 : extension_strength_safety_wit_1.
Axiom proof_of_extension_strength_safety_wit_2 : extension_strength_safety_wit_2.
Axiom proof_of_extension_strength_safety_wit_3 : extension_strength_safety_wit_3.
Axiom proof_of_extension_strength_safety_wit_4 : extension_strength_safety_wit_4.
Axiom proof_of_extension_strength_safety_wit_5 : extension_strength_safety_wit_5.
Axiom proof_of_extension_strength_safety_wit_6 : extension_strength_safety_wit_6.
Axiom proof_of_extension_strength_safety_wit_7 : extension_strength_safety_wit_7.
Axiom proof_of_extension_strength_safety_wit_8 : extension_strength_safety_wit_8.
Axiom proof_of_extension_strength_safety_wit_9 : extension_strength_safety_wit_9.
Axiom proof_of_extension_strength_safety_wit_10 : extension_strength_safety_wit_10.
Axiom proof_of_extension_strength_safety_wit_11 : extension_strength_safety_wit_11.
Axiom proof_of_extension_strength_safety_wit_12 : extension_strength_safety_wit_12.
Axiom proof_of_extension_strength_safety_wit_13 : extension_strength_safety_wit_13.
Axiom proof_of_extension_strength_safety_wit_14 : extension_strength_safety_wit_14.
Axiom proof_of_extension_strength_safety_wit_15 : extension_strength_safety_wit_15.
Axiom proof_of_extension_strength_safety_wit_16 : extension_strength_safety_wit_16.
Axiom proof_of_extension_strength_safety_wit_17 : extension_strength_safety_wit_17.
Axiom proof_of_extension_strength_safety_wit_18 : extension_strength_safety_wit_18.
Axiom proof_of_extension_strength_safety_wit_19 : extension_strength_safety_wit_19.
Axiom proof_of_extension_strength_safety_wit_20 : extension_strength_safety_wit_20.
Axiom proof_of_extension_strength_safety_wit_21 : extension_strength_safety_wit_21.
Axiom proof_of_extension_strength_safety_wit_22 : extension_strength_safety_wit_22.
Axiom proof_of_extension_strength_safety_wit_23 : extension_strength_safety_wit_23.
Axiom proof_of_extension_strength_safety_wit_24 : extension_strength_safety_wit_24.
Axiom proof_of_extension_strength_safety_wit_25 : extension_strength_safety_wit_25.
Axiom proof_of_extension_strength_entail_wit_1 : extension_strength_entail_wit_1.
Axiom proof_of_extension_strength_entail_wit_2 : extension_strength_entail_wit_2.
Axiom proof_of_extension_strength_entail_wit_3_1 : extension_strength_entail_wit_3_1.
Axiom proof_of_extension_strength_entail_wit_3_2 : extension_strength_entail_wit_3_2.
Axiom proof_of_extension_strength_entail_wit_3_3 : extension_strength_entail_wit_3_3.
Axiom proof_of_extension_strength_entail_wit_3_4 : extension_strength_entail_wit_3_4.
Axiom proof_of_extension_strength_entail_wit_3_5 : extension_strength_entail_wit_3_5.
Axiom proof_of_extension_strength_entail_wit_4 : extension_strength_entail_wit_4.
Axiom proof_of_extension_strength_return_wit_1 : extension_strength_return_wit_1.
Axiom proof_of_extension_strength_partial_solve_wit_1_pure : extension_strength_partial_solve_wit_1_pure.
Axiom proof_of_extension_strength_partial_solve_wit_1 : extension_strength_partial_solve_wit_1.
Axiom proof_of_Strongest_Extension_safety_wit_1 : Strongest_Extension_safety_wit_1.
Axiom proof_of_Strongest_Extension_safety_wit_2 : Strongest_Extension_safety_wit_2.
Axiom proof_of_Strongest_Extension_safety_wit_3 : Strongest_Extension_safety_wit_3.
Axiom proof_of_Strongest_Extension_safety_wit_4 : Strongest_Extension_safety_wit_4.
Axiom proof_of_Strongest_Extension_safety_wit_5 : Strongest_Extension_safety_wit_5.
Axiom proof_of_Strongest_Extension_safety_wit_6 : Strongest_Extension_safety_wit_6.
Axiom proof_of_Strongest_Extension_safety_wit_7 : Strongest_Extension_safety_wit_7.
Axiom proof_of_Strongest_Extension_safety_wit_8 : Strongest_Extension_safety_wit_8.
Axiom proof_of_Strongest_Extension_safety_wit_9 : Strongest_Extension_safety_wit_9.
Axiom proof_of_Strongest_Extension_safety_wit_10 : Strongest_Extension_safety_wit_10.
Axiom proof_of_Strongest_Extension_safety_wit_11 : Strongest_Extension_safety_wit_11.
Axiom proof_of_Strongest_Extension_safety_wit_12 : Strongest_Extension_safety_wit_12.
Axiom proof_of_Strongest_Extension_safety_wit_13 : Strongest_Extension_safety_wit_13.
Axiom proof_of_Strongest_Extension_safety_wit_14 : Strongest_Extension_safety_wit_14.
Axiom proof_of_Strongest_Extension_safety_wit_15 : Strongest_Extension_safety_wit_15.
Axiom proof_of_Strongest_Extension_safety_wit_16 : Strongest_Extension_safety_wit_16.
Axiom proof_of_Strongest_Extension_safety_wit_17 : Strongest_Extension_safety_wit_17.
Axiom proof_of_Strongest_Extension_safety_wit_18 : Strongest_Extension_safety_wit_18.
Axiom proof_of_Strongest_Extension_safety_wit_19 : Strongest_Extension_safety_wit_19.
Axiom proof_of_Strongest_Extension_safety_wit_20 : Strongest_Extension_safety_wit_20.
Axiom proof_of_Strongest_Extension_safety_wit_21 : Strongest_Extension_safety_wit_21.
Axiom proof_of_Strongest_Extension_safety_wit_22 : Strongest_Extension_safety_wit_22.
Axiom proof_of_Strongest_Extension_safety_wit_23 : Strongest_Extension_safety_wit_23.
Axiom proof_of_Strongest_Extension_entail_wit_1 : Strongest_Extension_entail_wit_1.
Axiom proof_of_Strongest_Extension_entail_wit_2 : Strongest_Extension_entail_wit_2.
Axiom proof_of_Strongest_Extension_entail_wit_3 : Strongest_Extension_entail_wit_3.
Axiom proof_of_Strongest_Extension_entail_wit_4 : Strongest_Extension_entail_wit_4.
Axiom proof_of_Strongest_Extension_entail_wit_5 : Strongest_Extension_entail_wit_5.
Axiom proof_of_Strongest_Extension_entail_wit_6 : Strongest_Extension_entail_wit_6.
Axiom proof_of_Strongest_Extension_entail_wit_7 : Strongest_Extension_entail_wit_7.
Axiom proof_of_Strongest_Extension_entail_wit_8_1 : Strongest_Extension_entail_wit_8_1.
Axiom proof_of_Strongest_Extension_entail_wit_8_2 : Strongest_Extension_entail_wit_8_2.
Axiom proof_of_Strongest_Extension_entail_wit_9 : Strongest_Extension_entail_wit_9.
Axiom proof_of_Strongest_Extension_entail_wit_10 : Strongest_Extension_entail_wit_10.
Axiom proof_of_Strongest_Extension_entail_wit_11 : Strongest_Extension_entail_wit_11.
Axiom proof_of_Strongest_Extension_entail_wit_12 : Strongest_Extension_entail_wit_12.
Axiom proof_of_Strongest_Extension_entail_wit_13 : Strongest_Extension_entail_wit_13.
Axiom proof_of_Strongest_Extension_entail_wit_14 : Strongest_Extension_entail_wit_14.
Axiom proof_of_Strongest_Extension_entail_wit_15 : Strongest_Extension_entail_wit_15.
Axiom proof_of_Strongest_Extension_entail_wit_16 : Strongest_Extension_entail_wit_16.
Axiom proof_of_Strongest_Extension_entail_wit_17 : Strongest_Extension_entail_wit_17.
Axiom proof_of_Strongest_Extension_return_wit_1 : Strongest_Extension_return_wit_1.
Axiom proof_of_Strongest_Extension_partial_solve_wit_1_pure : Strongest_Extension_partial_solve_wit_1_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_1 : Strongest_Extension_partial_solve_wit_1.
Axiom proof_of_Strongest_Extension_partial_solve_wit_2_pure : Strongest_Extension_partial_solve_wit_2_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_2 : Strongest_Extension_partial_solve_wit_2.
Axiom proof_of_Strongest_Extension_partial_solve_wit_3_pure : Strongest_Extension_partial_solve_wit_3_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_3 : Strongest_Extension_partial_solve_wit_3.
Axiom proof_of_Strongest_Extension_partial_solve_wit_4_pure : Strongest_Extension_partial_solve_wit_4_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_4 : Strongest_Extension_partial_solve_wit_4.
Axiom proof_of_Strongest_Extension_partial_solve_wit_5_pure : Strongest_Extension_partial_solve_wit_5_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_5 : Strongest_Extension_partial_solve_wit_5.
Axiom proof_of_Strongest_Extension_partial_solve_wit_6_pure : Strongest_Extension_partial_solve_wit_6_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_6 : Strongest_Extension_partial_solve_wit_6.
Axiom proof_of_Strongest_Extension_partial_solve_wit_7 : Strongest_Extension_partial_solve_wit_7.
Axiom proof_of_Strongest_Extension_partial_solve_wit_8_pure : Strongest_Extension_partial_solve_wit_8_pure.
Axiom proof_of_Strongest_Extension_partial_solve_wit_8 : Strongest_Extension_partial_solve_wit_8.
Axiom proof_of_Strongest_Extension_partial_solve_wit_9 : Strongest_Extension_partial_solve_wit_9.

End VC_Correct.
