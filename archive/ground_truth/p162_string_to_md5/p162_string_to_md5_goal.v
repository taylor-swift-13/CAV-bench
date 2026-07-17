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
Require Import p162_string_to_md5.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function md5_hex_digit_c -----*)

Definition md5_hex_digit_c_safety_wit_1 := 
forall (n_pre: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition md5_hex_digit_c_safety_wit_2 := 
forall (n_pre: Z) (PreH1 : (n_pre < 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((48 + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + n_pre )) ”
.

Definition md5_hex_digit_c_safety_wit_3 := 
forall (n_pre: Z) (PreH1 : (n_pre < 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition md5_hex_digit_c_safety_wit_4 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((97 + n_pre ) - 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((97 + n_pre ) - 10 )) ”
.

Definition md5_hex_digit_c_safety_wit_5 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((97 + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (97 + n_pre )) ”
.

Definition md5_hex_digit_c_safety_wit_6 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition md5_hex_digit_c_safety_wit_7 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition md5_hex_digit_c_return_wit_1 := 
(
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  TT && emp 
|--
  “ (((97 + n_pre ) - 10 ) = (md5_hex_digit_z (n_pre))) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  TT && emp 
|--
  “ (((97 + n_pre ) - 10 ) = (md5_hex_digit_z (n_pre))) ”
  &&  emp
).

Definition md5_hex_digit_c_return_wit_1_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (n_pre >= 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  (((97 + n_pre ) - 10 ) = (md5_hex_digit_z (n_pre)))
.

Definition md5_hex_digit_c_return_wit_2 := 
(
forall (n_pre: Z) (PreH1 : (n_pre < 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  TT && emp 
|--
  “ ((48 + n_pre ) = (md5_hex_digit_z (n_pre))) ”
  &&  emp
) \/
(
forall (n_pre: Z) (PreH1 : (n_pre < 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  TT && emp 
|--
  “ ((48 + n_pre ) = (md5_hex_digit_z (n_pre))) ”
  &&  emp
).

Definition md5_hex_digit_c_return_wit_2_split_goal_1 := 
forall (n_pre: Z) (PreH1 : (n_pre < 10)) (PreH2 : (0 <= n_pre)) (PreH3 : (n_pre < 16)) ,
  ((48 + n_pre ) = (md5_hex_digit_z (n_pre)))
.

(*----- Function string_to_md5 -----*)

Definition string_to_md5_safety_wit_1 := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : (valid_string input_s )) (PreH2 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH3 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_2 := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : (valid_string input_s )) (PreH2 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH3 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_3 := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition string_to_md5_safety_wit_4 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (UCharArray.undef_full retval 16 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_5 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (md5_digest_ok_z input_s )) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH5 : (valid_string input_s )) (PreH6 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH7 : (problem_162_pre_z input_s )) ,
  (store_string text_pre input_s )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition string_to_md5_safety_wit_6 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (md5_digest_ok_z input_s )) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input_s)) + 1 ))) (PreH5 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH6 : (valid_string input_s )) (PreH7 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH8 : (problem_162_pre_z input_s )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 33 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval_2)
  **  ((( &( "md" ) )) # Ptr  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_7 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 16)) (PreH3 : (0 < (string_length (input_s)))) (PreH4 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH5 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH6 : ((Zlength (output)) = (2 * i ))) (PreH7 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  (store_string text input_s )
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition string_to_md5_safety_wit_8 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) <> (INT_MIN)) \/ (16 <> (-1))) ” 
  &&  “ (16 <> 0) ”
.

Definition string_to_md5_safety_wit_9 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "hi" ) )) # Int  |->_)
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition string_to_md5_safety_wit_10 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) <> (INT_MIN)) \/ (16 <> (-1))) ” 
  &&  “ (16 <> 0) ”
.

Definition string_to_md5_safety_wit_11 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition string_to_md5_safety_wit_12 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition string_to_md5_safety_wit_13 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition string_to_md5_safety_wit_14 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (((2 * i ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((2 * i ) + 1 )) ”
.

Definition string_to_md5_safety_wit_15 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ ((2 * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (2 * i )) ”
.

Definition string_to_md5_safety_wit_16 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition string_to_md5_safety_wit_17 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_to_md5_safety_wit_18 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))))) (PreH2 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : (i < 16)) (PreH5 : (0 <= i)) (PreH6 : (i <= 16)) (PreH7 : (0 < (string_length (input_s)))) (PreH8 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH10 : ((Zlength (output)) = (2 * i ))) (PreH11 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 (((2 * i ) + 1 ) + 1 ) (app ((app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z)))))) ((cons ((signed_last_nbits (retval_2) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str (((2 * i ) + 1 ) + 1 ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition string_to_md5_safety_wit_19 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i >= 16)) (PreH2 : (0 <= i)) (PreH3 : (i <= 16)) (PreH4 : (0 < (string_length (input_s)))) (PreH5 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH7 : ((Zlength (output)) = (2 * i ))) (PreH8 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  (store_string text input_s )
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (16 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 16) ”
.

Definition string_to_md5_safety_wit_20 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i >= 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition string_to_md5_safety_wit_21 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i >= 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_22 := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition string_to_md5_safety_wit_23 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_safety_wit_24 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (78 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 78) ”
.

Definition string_to_md5_safety_wit_25 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.undef_seg retval 1 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition string_to_md5_safety_wit_26 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.undef_seg retval 1 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition string_to_md5_safety_wit_27 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition string_to_md5_safety_wit_28 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (110 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 110) ”
.

Definition string_to_md5_safety_wit_29 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval ((1 + 1 ) + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition string_to_md5_safety_wit_30 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval ((1 + 1 ) + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition string_to_md5_safety_wit_31 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (((1 + 1 ) + 1 ) + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition string_to_md5_safety_wit_32 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (((1 + 1 ) + 1 ) + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> retval)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition string_to_md5_entail_wit_1 := 
(
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (md5_digest_ok_z input_s )) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input_s)) + 1 ))) (PreH5 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH6 : (valid_string input_s )) (PreH7 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH8 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_full retval_2 33 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
|--
  EX (output: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * 0 )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) 0 output ) ”
  &&  (store_string text_pre input_s )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
  **  (CharArray.seg retval_2 0 (2 * 0 ) output )
  **  (CharArray.undef_seg retval_2 (2 * 0 ) 33 )
) \/
(
forall (input_s: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (md5_digest_ok_z input_s )) (PreH3 : (retval <> 0)) (PreH4 : (0 <= ((string_length (input_s)) + 1 ))) (PreH5 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH6 : (valid_string input_s )) (PreH7 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH8 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_full retval_2 33 )
|--
  EX (output: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * 0 )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) 0 output ) ”
  &&  (CharArray.undef_full retval_2 33 )
  **  (CharArray.seg retval_2 0 (2 * 0 ) output )
).

Definition string_to_md5_entail_wit_2 := 
(
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output_2: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))))) (PreH2 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : (i < 16)) (PreH5 : (0 <= i)) (PreH6 : (i <= 16)) (PreH7 : (0 < (string_length (input_s)))) (PreH8 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH10 : ((Zlength (output_2)) = (2 * i ))) (PreH11 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output_2 )) ,
  (CharArray.seg out_str 0 (((2 * i ) + 1 ) + 1 ) (app ((app (output_2) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z)))))) ((cons ((signed_last_nbits (retval_2) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str (((2 * i ) + 1 ) + 1 ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  EX (output: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * (i + 1 ) )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) (i + 1 ) output ) ”
  &&  (store_string text input_s )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.seg out_str 0 (2 * (i + 1 ) ) output )
  **  (CharArray.undef_seg out_str (2 * (i + 1 ) ) 33 )
) \/
(
forall (input_s: (@list Z)) (out_str: Z) (output_2: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))))) (PreH2 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : (i < 16)) (PreH5 : (0 <= i)) (PreH6 : (i <= 16)) (PreH7 : (0 < (string_length (input_s)))) (PreH8 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH10 : ((Zlength (output_2)) = (2 * i ))) (PreH11 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output_2 )) ,
  (CharArray.seg out_str 0 (((2 * i ) + 1 ) + 1 ) (app ((app (output_2) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z)))))) ((cons ((signed_last_nbits (retval_2) (8))) ((@nil Z))))) )
|--
  EX (output: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * (i + 1 ) )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) (i + 1 ) output ) ”
  &&  (CharArray.seg out_str 0 (2 * (i + 1 ) ) output )
).

Definition string_to_md5_return_wit_1 := 
(
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval ((((1 + 1 ) + 1 ) + 1 ) + 1 ) 5 )
  **  (((retval + (4 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  EX (preserved_text_2: Z)  (output_s: (@list Z)) ,
  “ (problem_162_spec_z input_s output_s ) ”
  &&  (store_string preserved_text_2 input_s )
  **  (CharArray.full retval ((Zlength (output_s)) + 1 ) (app (output_s) ((cons (0) ((@nil Z))))) )
) \/
(
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (((retval + (4 * sizeof(CHAR)))) # Char  |-> 0)
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  EX (preserved_text_2: Z)  (output_s: (@list Z)) ,
  “ (problem_162_spec_z input_s output_s ) ”
  &&  (CharArray.full preserved_text_2 ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.full retval ((Zlength (output_s)) + 1 ) (app (output_s) ((cons (0) ((@nil Z))))) )
).

Definition string_to_md5_return_wit_2 := 
forall (input_s: (@list Z)) (out_str: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i >= 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  (EX (preserved_text: Z) ,
  “ (out_str = 0) ”
  &&  (store_string preserved_text input_s ))
  ||
  (EX (preserved_text_2: Z)  (output_s: (@list Z)) ,
  “ (problem_162_spec_z input_s output_s ) ”
  &&  (store_string preserved_text_2 input_s )
  **  (CharArray.full out_str ((Zlength (output_s)) + 1 ) (app (output_s) ((cons (0) ((@nil Z))))) ))
.

Definition string_to_md5_partial_solve_wit_1_pure := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (0 <= 16) ” 
  &&  “ (16 < INT_MAX) ”
.

Definition string_to_md5_partial_solve_wit_1_aux := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  (store_string text_pre input_s )
|--
  “ (0 <= 16) ” 
  &&  “ (16 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) <> 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_1 := string_to_md5_partial_solve_wit_1_pure -> string_to_md5_partial_solve_wit_1_aux.

Definition string_to_md5_partial_solve_wit_2 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (UCharArray.undef_full retval 16 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) <> 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (store_string text_pre input_s )
  **  (UCharArray.undef_full retval 16 )
.

Definition string_to_md5_partial_solve_wit_3_pure := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (md5_digest_ok_z input_s )) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH5 : (valid_string input_s )) (PreH6 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH7 : (problem_162_pre_z input_s )) ,
  (store_string text_pre input_s )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |-> retval)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= 33) ” 
  &&  “ (33 < INT_MAX) ”
.

Definition string_to_md5_partial_solve_wit_3_aux := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (md5_digest_ok_z input_s )) (PreH2 : (retval <> 0)) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : ((Znth 0 (c_string (input_s)) 0) <> 0)) (PreH5 : (valid_string input_s )) (PreH6 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH7 : (problem_162_pre_z input_s )) ,
  (store_string text_pre input_s )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
|--
  “ (0 <= 33) ” 
  &&  “ (33 < INT_MAX) ” 
  &&  “ (md5_digest_ok_z input_s ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) <> 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (UCharArray.full retval 16 (md5_digest_z (input_s)) )
.

Definition string_to_md5_partial_solve_wit_3 := string_to_md5_partial_solve_wit_3_pure -> string_to_md5_partial_solve_wit_3_aux.

Definition string_to_md5_partial_solve_wit_4 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i < 16)) (PreH2 : (0 <= i)) (PreH3 : (i <= 16)) (PreH4 : (0 < (string_length (input_s)))) (PreH5 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH7 : ((Zlength (output)) = (2 * i ))) (PreH8 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (store_string text input_s )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i < 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (((md + (i * sizeof(UCHAR)))) # UChar  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  (UCharArray.missing_i md i 0 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
.

Definition string_to_md5_partial_solve_wit_5_pure := 
(
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) < 16) ” 
  &&  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )) ”
) \/
(
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (0 <= ((string_length (input_s)) + 1 ))) (PreH10 : (i < 16)) (PreH11 : (0 <= i)) (PreH12 : (i <= 16)) (PreH13 : (0 < (string_length (input_s)))) (PreH14 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH16 : ((Zlength (output)) = (2 * i ))) (PreH17 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )) ” 
  &&  “ (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) < 16) ”
).

Definition string_to_md5_partial_solve_wit_5_pure_split_goal_1 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (0 <= ((string_length (input_s)) + 1 ))) (PreH10 : (i < 16)) (PreH11 : (0 <= i)) (PreH12 : (i <= 16)) (PreH13 : (0 < (string_length (input_s)))) (PreH14 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH16 : ((Zlength (output)) = (2 * i ))) (PreH17 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )) ”
.

Definition string_to_md5_partial_solve_wit_5_pure_split_goal_2 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (0 <= ((string_length (input_s)) + 1 ))) (PreH10 : (i < 16)) (PreH11 : (0 <= i)) (PreH12 : (i <= 16)) (PreH13 : (0 < (string_length (input_s)))) (PreH14 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH15 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH16 : ((Zlength (output)) = (2 * i ))) (PreH17 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) < 16) ”
.

Definition string_to_md5_partial_solve_wit_5_aux := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i < 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) < 16) ” 
  &&  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i < 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
.

Definition string_to_md5_partial_solve_wit_5 := string_to_md5_partial_solve_wit_5_pure -> string_to_md5_partial_solve_wit_5_aux.

Definition string_to_md5_partial_solve_wit_6 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )))) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i < 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (((out_str + ((2 * i ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_str (2 * i ) (2 * i ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
.

Definition string_to_md5_partial_solve_wit_7_pure := 
(
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) < 16) ” 
  &&  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) )) ”
) \/
(
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH10 : (0 <= ((string_length (input_s)) + 1 ))) (PreH11 : (i < 16)) (PreH12 : (0 <= i)) (PreH13 : (i <= 16)) (PreH14 : (0 < (string_length (input_s)))) (PreH15 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH17 : ((Zlength (output)) = (2 * i ))) (PreH18 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) )) ” 
  &&  “ (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) < 16) ”
).

Definition string_to_md5_partial_solve_wit_7_pure_split_goal_1 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH10 : (0 <= ((string_length (input_s)) + 1 ))) (PreH11 : (i < 16)) (PreH12 : (0 <= i)) (PreH13 : (i <= 16)) (PreH14 : (0 < (string_length (input_s)))) (PreH15 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH17 : ((Zlength (output)) = (2 * i ))) (PreH18 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) )) ”
.

Definition string_to_md5_partial_solve_wit_7_pure_split_goal_2 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (i <= INT_MAX)) (PreH2 : ((Znth i (md5_digest_z (input_s)) 0) <= INT_MAX)) (PreH3 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) <= INT_MAX)) (PreH4 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) <= INT_MAX)) (PreH5 : (i >= INT_MIN)) (PreH6 : ((Znth i (md5_digest_z (input_s)) 0) >= INT_MIN)) (PreH7 : (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ) >= INT_MIN)) (PreH8 : (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) >= INT_MIN)) (PreH9 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH10 : (0 <= ((string_length (input_s)) + 1 ))) (PreH11 : (i < 16)) (PreH12 : (0 <= i)) (PreH13 : (i <= 16)) (PreH14 : (0 < (string_length (input_s)))) (PreH15 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH16 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH17 : ((Zlength (output)) = (2 * i ))) (PreH18 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  ((( &( "lo" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))
  **  ((( &( "hi" ) )) # Int  |-> ((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  ((( &( "byte" ) )) # Int  |-> (Znth i (md5_digest_z (input_s)) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) < 16) ”
.

Definition string_to_md5_partial_solve_wit_7_aux := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (PreH1 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : (i < 16)) (PreH4 : (0 <= i)) (PreH5 : (i <= 16)) (PreH6 : (0 < (string_length (input_s)))) (PreH7 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH8 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH9 : ((Zlength (output)) = (2 * i ))) (PreH10 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ) < 16) ” 
  &&  “ (0 <= ((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) )) ” 
  &&  “ (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )))) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i < 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_7 := string_to_md5_partial_solve_wit_7_pure -> string_to_md5_partial_solve_wit_7_aux.

Definition string_to_md5_partial_solve_wit_8 := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) ))))) (PreH2 : (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 ))))) (PreH3 : (0 <= ((string_length (input_s)) + 1 ))) (PreH4 : (i < 16)) (PreH5 : (0 <= i)) (PreH6 : (i <= 16)) (PreH7 : (0 < (string_length (input_s)))) (PreH8 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH9 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH10 : ((Zlength (output)) = (2 * i ))) (PreH11 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (CharArray.undef_seg out_str ((2 * i ) + 1 ) 33 )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval_2 = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) % ( 16 ) )))) ” 
  &&  “ (retval = (md5_hex_digit_z (((Znth i (md5_digest_z (input_s)) 0) ÷ 16 )))) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i < 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (((out_str + (((2 * i ) + 1 ) * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_str ((2 * i ) + 1 ) ((2 * i ) + 1 ) 33 )
  **  (CharArray.seg out_str 0 ((2 * i ) + 1 ) (app (output) ((cons ((signed_last_nbits (retval) (8))) ((@nil Z))))) )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_9_pure := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i >= 16)) (PreH2 : (0 <= i)) (PreH3 : (i <= 16)) (PreH4 : (0 < (string_length (input_s)))) (PreH5 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH7 : ((Zlength (output)) = (2 * i ))) (PreH8 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "text" ) )) # Ptr  |-> text)
  **  (store_string text input_s )
  **  ((( &( "md" ) )) # Ptr  |-> md)
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  ((( &( "out_str" ) )) # Ptr  |-> out_str)
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= 16) ” 
  &&  “ (16 < INT_MAX) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ”
.

Definition string_to_md5_partial_solve_wit_9_aux := 
forall (input_s: (@list Z)) (out_str: Z) (md: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (i >= 16)) (PreH2 : (0 <= i)) (PreH3 : (i <= 16)) (PreH4 : (0 < (string_length (input_s)))) (PreH5 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH6 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH7 : ((Zlength (output)) = (2 * i ))) (PreH8 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (store_string text input_s )
  **  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= 16) ” 
  &&  “ (16 < INT_MAX) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i >= 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (UCharArray.full md 16 (md5_digest_z (input_s)) )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
.

Definition string_to_md5_partial_solve_wit_9 := string_to_md5_partial_solve_wit_9_pure -> string_to_md5_partial_solve_wit_9_aux.

Definition string_to_md5_partial_solve_wit_10 := 
forall (input_s: (@list Z)) (out_str: Z) (text: Z) (output: (@list Z)) (i: Z) (PreH1 : (0 <= ((string_length (input_s)) + 1 ))) (PreH2 : (i >= 16)) (PreH3 : (0 <= i)) (PreH4 : (i <= 16)) (PreH5 : (0 < (string_length (input_s)))) (PreH6 : ((Zlength ((md5_digest_z (input_s)))) = 16)) (PreH7 : forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16)))) (PreH8 : ((Zlength (output)) = (2 * i ))) (PreH9 : (md5_hex_prefix_z (md5_digest_z (input_s)) i output )) ,
  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
  **  (CharArray.undef_seg out_str (2 * i ) 33 )
|--
  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ (i >= 16) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 16) ” 
  &&  “ (0 < (string_length (input_s))) ” 
  &&  “ ((Zlength ((md5_digest_z (input_s)))) = 16) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < 16)) -> ((((((0 <= (Znth (k) ((md5_digest_z (input_s))) (0))) /\ ((Znth (k) ((md5_digest_z (input_s))) (0)) < 256)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) ÷ 16 ) < 16)) /\ (0 <= ((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ))) /\ (((Znth (k) ((md5_digest_z (input_s))) (0)) % ( 16 ) ) < 16))) ” 
  &&  “ ((Zlength (output)) = (2 * i )) ” 
  &&  “ (md5_hex_prefix_z (md5_digest_z (input_s)) i output ) ”
  &&  (((out_str + (32 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i out_str 32 (2 * i ) 33 )
  **  (CharArray.full text ((string_length (input_s)) + 1 ) (c_string (input_s)) )
  **  (CharArray.seg out_str 0 (2 * i ) output )
.

Definition string_to_md5_partial_solve_wit_11_pure := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  ((( &( "out_str" ) )) # Ptr  |->_)
  **  ((( &( "md" ) )) # Ptr  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (store_string text_pre input_s )
|--
  “ (0 <= 5) ” 
  &&  “ (5 < INT_MAX) ”
.

Definition string_to_md5_partial_solve_wit_11_aux := 
forall (text_pre: Z) (input_s: (@list Z)) (PreH1 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH2 : (valid_string input_s )) (PreH3 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH4 : (problem_162_pre_z input_s )) ,
  (store_string text_pre input_s )
|--
  “ (0 <= 5) ” 
  &&  “ (5 < INT_MAX) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_11 := string_to_md5_partial_solve_wit_11_pure -> string_to_md5_partial_solve_wit_11_aux.

Definition string_to_md5_partial_solve_wit_12 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_full retval 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (((retval + (0 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_seg retval 1 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_13 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.undef_seg retval 1 5 )
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (((retval + (1 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 1 5 )
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_14 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (((retval + (2 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i retval 2 (1 + 1 ) 5 )
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_15 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval ((1 + 1 ) + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (((retval + (3 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i retval 3 ((1 + 1 ) + 1 ) 5 )
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Definition string_to_md5_partial_solve_wit_16 := 
forall (text_pre: Z) (input_s: (@list Z)) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (input_s)) + 1 ))) (PreH3 : ((Znth 0 (c_string (input_s)) 0) = 0)) (PreH4 : (valid_string input_s )) (PreH5 : (((string_length (input_s)) + 1 ) < INT_MAX)) (PreH6 : (problem_162_pre_z input_s )) ,
  (CharArray.undef_seg retval (((1 + 1 ) + 1 ) + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= ((string_length (input_s)) + 1 )) ” 
  &&  “ ((Znth 0 (c_string (input_s)) 0) = 0) ” 
  &&  “ (valid_string input_s ) ” 
  &&  “ (((string_length (input_s)) + 1 ) < INT_MAX) ” 
  &&  “ (problem_162_pre_z input_s ) ”
  &&  (((retval + (4 * sizeof(CHAR)))) # Char  |->_)
  **  (CharArray.undef_missing_i retval 4 (((1 + 1 ) + 1 ) + 1 ) 5 )
  **  (((retval + (3 * sizeof(CHAR)))) # Char  |-> 101)
  **  (((retval + (2 * sizeof(CHAR)))) # Char  |-> 110)
  **  (((retval + (1 * sizeof(CHAR)))) # Char  |-> 111)
  **  (((retval + (0 * sizeof(CHAR)))) # Char  |-> 78)
  **  (CharArray.full text_pre ((string_length (input_s)) + 1 ) (c_string (input_s)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_md5_hex_digit_c_safety_wit_1 : md5_hex_digit_c_safety_wit_1.
Axiom proof_of_md5_hex_digit_c_safety_wit_2 : md5_hex_digit_c_safety_wit_2.
Axiom proof_of_md5_hex_digit_c_safety_wit_3 : md5_hex_digit_c_safety_wit_3.
Axiom proof_of_md5_hex_digit_c_safety_wit_4 : md5_hex_digit_c_safety_wit_4.
Axiom proof_of_md5_hex_digit_c_safety_wit_5 : md5_hex_digit_c_safety_wit_5.
Axiom proof_of_md5_hex_digit_c_safety_wit_6 : md5_hex_digit_c_safety_wit_6.
Axiom proof_of_md5_hex_digit_c_safety_wit_7 : md5_hex_digit_c_safety_wit_7.
Axiom proof_of_md5_hex_digit_c_return_wit_1 : md5_hex_digit_c_return_wit_1.
Axiom proof_of_md5_hex_digit_c_return_wit_2 : md5_hex_digit_c_return_wit_2.
Axiom proof_of_string_to_md5_safety_wit_1 : string_to_md5_safety_wit_1.
Axiom proof_of_string_to_md5_safety_wit_2 : string_to_md5_safety_wit_2.
Axiom proof_of_string_to_md5_safety_wit_3 : string_to_md5_safety_wit_3.
Axiom proof_of_string_to_md5_safety_wit_4 : string_to_md5_safety_wit_4.
Axiom proof_of_string_to_md5_safety_wit_5 : string_to_md5_safety_wit_5.
Axiom proof_of_string_to_md5_safety_wit_6 : string_to_md5_safety_wit_6.
Axiom proof_of_string_to_md5_safety_wit_7 : string_to_md5_safety_wit_7.
Axiom proof_of_string_to_md5_safety_wit_8 : string_to_md5_safety_wit_8.
Axiom proof_of_string_to_md5_safety_wit_9 : string_to_md5_safety_wit_9.
Axiom proof_of_string_to_md5_safety_wit_10 : string_to_md5_safety_wit_10.
Axiom proof_of_string_to_md5_safety_wit_11 : string_to_md5_safety_wit_11.
Axiom proof_of_string_to_md5_safety_wit_12 : string_to_md5_safety_wit_12.
Axiom proof_of_string_to_md5_safety_wit_13 : string_to_md5_safety_wit_13.
Axiom proof_of_string_to_md5_safety_wit_14 : string_to_md5_safety_wit_14.
Axiom proof_of_string_to_md5_safety_wit_15 : string_to_md5_safety_wit_15.
Axiom proof_of_string_to_md5_safety_wit_16 : string_to_md5_safety_wit_16.
Axiom proof_of_string_to_md5_safety_wit_17 : string_to_md5_safety_wit_17.
Axiom proof_of_string_to_md5_safety_wit_18 : string_to_md5_safety_wit_18.
Axiom proof_of_string_to_md5_safety_wit_19 : string_to_md5_safety_wit_19.
Axiom proof_of_string_to_md5_safety_wit_20 : string_to_md5_safety_wit_20.
Axiom proof_of_string_to_md5_safety_wit_21 : string_to_md5_safety_wit_21.
Axiom proof_of_string_to_md5_safety_wit_22 : string_to_md5_safety_wit_22.
Axiom proof_of_string_to_md5_safety_wit_23 : string_to_md5_safety_wit_23.
Axiom proof_of_string_to_md5_safety_wit_24 : string_to_md5_safety_wit_24.
Axiom proof_of_string_to_md5_safety_wit_25 : string_to_md5_safety_wit_25.
Axiom proof_of_string_to_md5_safety_wit_26 : string_to_md5_safety_wit_26.
Axiom proof_of_string_to_md5_safety_wit_27 : string_to_md5_safety_wit_27.
Axiom proof_of_string_to_md5_safety_wit_28 : string_to_md5_safety_wit_28.
Axiom proof_of_string_to_md5_safety_wit_29 : string_to_md5_safety_wit_29.
Axiom proof_of_string_to_md5_safety_wit_30 : string_to_md5_safety_wit_30.
Axiom proof_of_string_to_md5_safety_wit_31 : string_to_md5_safety_wit_31.
Axiom proof_of_string_to_md5_safety_wit_32 : string_to_md5_safety_wit_32.
Axiom proof_of_string_to_md5_entail_wit_1 : string_to_md5_entail_wit_1.
Axiom proof_of_string_to_md5_entail_wit_2 : string_to_md5_entail_wit_2.
Axiom proof_of_string_to_md5_return_wit_1 : string_to_md5_return_wit_1.
Axiom proof_of_string_to_md5_return_wit_2 : string_to_md5_return_wit_2.
Axiom proof_of_string_to_md5_partial_solve_wit_1_pure : string_to_md5_partial_solve_wit_1_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_1 : string_to_md5_partial_solve_wit_1.
Axiom proof_of_string_to_md5_partial_solve_wit_2 : string_to_md5_partial_solve_wit_2.
Axiom proof_of_string_to_md5_partial_solve_wit_3_pure : string_to_md5_partial_solve_wit_3_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_3 : string_to_md5_partial_solve_wit_3.
Axiom proof_of_string_to_md5_partial_solve_wit_4 : string_to_md5_partial_solve_wit_4.
Axiom proof_of_string_to_md5_partial_solve_wit_5_pure : string_to_md5_partial_solve_wit_5_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_5 : string_to_md5_partial_solve_wit_5.
Axiom proof_of_string_to_md5_partial_solve_wit_6 : string_to_md5_partial_solve_wit_6.
Axiom proof_of_string_to_md5_partial_solve_wit_7_pure : string_to_md5_partial_solve_wit_7_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_7 : string_to_md5_partial_solve_wit_7.
Axiom proof_of_string_to_md5_partial_solve_wit_8 : string_to_md5_partial_solve_wit_8.
Axiom proof_of_string_to_md5_partial_solve_wit_9_pure : string_to_md5_partial_solve_wit_9_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_9 : string_to_md5_partial_solve_wit_9.
Axiom proof_of_string_to_md5_partial_solve_wit_10 : string_to_md5_partial_solve_wit_10.
Axiom proof_of_string_to_md5_partial_solve_wit_11_pure : string_to_md5_partial_solve_wit_11_pure.
Axiom proof_of_string_to_md5_partial_solve_wit_11 : string_to_md5_partial_solve_wit_11.
Axiom proof_of_string_to_md5_partial_solve_wit_12 : string_to_md5_partial_solve_wit_12.
Axiom proof_of_string_to_md5_partial_solve_wit_13 : string_to_md5_partial_solve_wit_13.
Axiom proof_of_string_to_md5_partial_solve_wit_14 : string_to_md5_partial_solve_wit_14.
Axiom proof_of_string_to_md5_partial_solve_wit_15 : string_to_md5_partial_solve_wit_15.
Axiom proof_of_string_to_md5_partial_solve_wit_16 : string_to_md5_partial_solve_wit_16.

End VC_Correct.
