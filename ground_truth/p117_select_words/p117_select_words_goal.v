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
Require Import p117_select_words.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import ptr_array2_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.
From SimpleC.StdLib Require Import string_strategy_goal.
From SimpleC.StdLib Require Import string_strategy_proof.

(*----- Function is_consonant_char -----*)

Definition is_consonant_char_safety_wit_1 := 
forall (ch_pre: Z) (PreH1 : (0 <= ch_pre)) (PreH2 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_consonant_char_safety_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 65)) (PreH2 : (0 <= ch_pre)) (PreH3 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition is_consonant_char_safety_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 90)) (PreH2 : (ch_pre >= 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_consonant_char_safety_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 65)) (PreH2 : (0 <= ch_pre)) (PreH3 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_consonant_char_safety_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre >= 97)) (PreH2 : (ch_pre > 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition is_consonant_char_safety_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 122)) (PreH2 : (ch_pre >= 97)) (PreH3 : (ch_pre > 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_consonant_char_safety_wit_8 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <= 90)) (PreH2 : (ch_pre >= 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_consonant_char_safety_wit_9 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 65)) (PreH2 : (ch_pre <= 122)) (PreH3 : (ch_pre >= 97)) (PreH4 : (ch_pre > 90)) (PreH5 : (ch_pre >= 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_10 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 65)) (PreH2 : (ch_pre <= 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition is_consonant_char_safety_wit_11 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 65)) (PreH2 : (ch_pre <= 122)) (PreH3 : (ch_pre >= 97)) (PreH4 : (ch_pre > 90)) (PreH5 : (ch_pre >= 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition is_consonant_char_safety_wit_12 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (ch_pre <= 122)) (PreH4 : (ch_pre >= 97)) (PreH5 : (ch_pre > 90)) (PreH6 : (ch_pre >= 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_13 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (ch_pre <= 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_consonant_char_safety_wit_14 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (ch_pre <= 122)) (PreH4 : (ch_pre >= 97)) (PreH5 : (ch_pre > 90)) (PreH6 : (ch_pre >= 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_consonant_char_safety_wit_15 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (ch_pre <= 122)) (PreH5 : (ch_pre >= 97)) (PreH6 : (ch_pre > 90)) (PreH7 : (ch_pre >= 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_16 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (ch_pre <= 90)) (PreH5 : (ch_pre >= 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition is_consonant_char_safety_wit_17 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (ch_pre <= 122)) (PreH5 : (ch_pre >= 97)) (PreH6 : (ch_pre > 90)) (PreH7 : (ch_pre >= 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition is_consonant_char_safety_wit_18 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (ch_pre <= 122)) (PreH6 : (ch_pre >= 97)) (PreH7 : (ch_pre > 90)) (PreH8 : (ch_pre >= 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_19 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (ch_pre <= 90)) (PreH6 : (ch_pre >= 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition is_consonant_char_safety_wit_20 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (ch_pre <= 122)) (PreH6 : (ch_pre >= 97)) (PreH7 : (ch_pre > 90)) (PreH8 : (ch_pre >= 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition is_consonant_char_safety_wit_21 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (ch_pre <= 122)) (PreH7 : (ch_pre >= 97)) (PreH8 : (ch_pre > 90)) (PreH9 : (ch_pre >= 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_22 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (ch_pre <= 90)) (PreH7 : (ch_pre >= 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_consonant_char_safety_wit_23 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (ch_pre <= 122)) (PreH7 : (ch_pre >= 97)) (PreH8 : (ch_pre > 90)) (PreH9 : (ch_pre >= 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_consonant_char_safety_wit_24 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (ch_pre <= 90)) (PreH8 : (ch_pre >= 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_25 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (ch_pre <= 90)) (PreH8 : (ch_pre >= 65)) (PreH9 : (0 <= ch_pre)) (PreH10 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition is_consonant_char_safety_wit_26 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (ch_pre <= 122)) (PreH8 : (ch_pre >= 97)) (PreH9 : (ch_pre > 90)) (PreH10 : (ch_pre >= 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition is_consonant_char_safety_wit_27 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (ch_pre <= 90)) (PreH9 : (ch_pre >= 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_28 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (ch_pre <= 90)) (PreH9 : (ch_pre >= 65)) (PreH10 : (0 <= ch_pre)) (PreH11 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition is_consonant_char_safety_wit_29 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (ch_pre <= 122)) (PreH9 : (ch_pre >= 97)) (PreH10 : (ch_pre > 90)) (PreH11 : (ch_pre >= 65)) (PreH12 : (0 <= ch_pre)) (PreH13 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition is_consonant_char_safety_wit_30 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (ch_pre <= 90)) (PreH10 : (ch_pre >= 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_31 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (ch_pre <= 90)) (PreH10 : (ch_pre >= 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition is_consonant_char_safety_wit_32 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (ch_pre <= 122)) (PreH10 : (ch_pre >= 97)) (PreH11 : (ch_pre > 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition is_consonant_char_safety_wit_33 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (ch_pre <= 90)) (PreH11 : (ch_pre >= 65)) (PreH12 : (0 <= ch_pre)) (PreH13 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_34 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (ch_pre <= 90)) (PreH11 : (ch_pre >= 65)) (PreH12 : (0 <= ch_pre)) (PreH13 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition is_consonant_char_safety_wit_35 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (ch_pre <= 122)) (PreH11 : (ch_pre >= 97)) (PreH12 : (ch_pre > 90)) (PreH13 : (ch_pre >= 65)) (PreH14 : (0 <= ch_pre)) (PreH15 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition is_consonant_char_safety_wit_36 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ False ”
.

Definition is_consonant_char_safety_wit_37 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_consonant_char_safety_wit_38 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 122)) (PreH12 : (ch_pre >= 97)) (PreH13 : (ch_pre > 90)) (PreH14 : (ch_pre >= 65)) (PreH15 : (0 <= ch_pre)) (PreH16 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_consonant_char_safety_wit_39 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_40 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre > 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_41 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 122)) (PreH2 : (ch_pre >= 97)) (PreH3 : (ch_pre > 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_42 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 122)) (PreH12 : (ch_pre >= 97)) (PreH13 : (ch_pre > 90)) (PreH14 : (ch_pre >= 65)) (PreH15 : (0 <= ch_pre)) (PreH16 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_43 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (ch_pre <= 122)) (PreH10 : (ch_pre >= 97)) (PreH11 : (ch_pre > 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_44 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (ch_pre <= 122)) (PreH8 : (ch_pre >= 97)) (PreH9 : (ch_pre > 90)) (PreH10 : (ch_pre >= 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_45 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (ch_pre <= 90)) (PreH6 : (ch_pre >= 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_46 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (ch_pre <= 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_47 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 65)) (PreH2 : (ch_pre <= 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_48 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (ch_pre <= 90)) (PreH5 : (ch_pre >= 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_49 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (ch_pre <= 90)) (PreH7 : (ch_pre >= 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_50 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (ch_pre <= 122)) (PreH9 : (ch_pre >= 97)) (PreH10 : (ch_pre > 90)) (PreH11 : (ch_pre >= 65)) (PreH12 : (0 <= ch_pre)) (PreH13 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_safety_wit_51 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (ch_pre <= 122)) (PreH11 : (ch_pre >= 97)) (PreH12 : (ch_pre > 90)) (PreH13 : (ch_pre >= 65)) (PreH14 : (0 <= ch_pre)) (PreH15 : (ch_pre <= 127)) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_consonant_char_return_wit_1 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre < 65)) (PreH3 : (0 <= ch_pre)) (PreH4 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_2 := 
forall (ch_pre: Z) (PreH1 : (ch_pre < 97)) (PreH2 : (ch_pre > 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_3 := 
forall (ch_pre: Z) (PreH1 : (ch_pre > 122)) (PreH2 : (ch_pre >= 97)) (PreH3 : (ch_pre > 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_4 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 122)) (PreH12 : (ch_pre >= 97)) (PreH13 : (ch_pre > 90)) (PreH14 : (ch_pre >= 65)) (PreH15 : (0 <= ch_pre)) (PreH16 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_5 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 105)) (PreH2 : (ch_pre <> 101)) (PreH3 : (ch_pre <> 97)) (PreH4 : (ch_pre <> 85)) (PreH5 : (ch_pre <> 79)) (PreH6 : (ch_pre <> 73)) (PreH7 : (ch_pre <> 69)) (PreH8 : (ch_pre <> 65)) (PreH9 : (ch_pre <= 122)) (PreH10 : (ch_pre >= 97)) (PreH11 : (ch_pre > 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_6 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 97)) (PreH2 : (ch_pre <> 85)) (PreH3 : (ch_pre <> 79)) (PreH4 : (ch_pre <> 73)) (PreH5 : (ch_pre <> 69)) (PreH6 : (ch_pre <> 65)) (PreH7 : (ch_pre <= 122)) (PreH8 : (ch_pre >= 97)) (PreH9 : (ch_pre > 90)) (PreH10 : (ch_pre >= 65)) (PreH11 : (0 <= ch_pre)) (PreH12 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_7 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 79)) (PreH2 : (ch_pre <> 73)) (PreH3 : (ch_pre <> 69)) (PreH4 : (ch_pre <> 65)) (PreH5 : (ch_pre <= 90)) (PreH6 : (ch_pre >= 65)) (PreH7 : (0 <= ch_pre)) (PreH8 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_8 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 69)) (PreH2 : (ch_pre <> 65)) (PreH3 : (ch_pre <= 90)) (PreH4 : (ch_pre >= 65)) (PreH5 : (0 <= ch_pre)) (PreH6 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_9 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 65)) (PreH2 : (ch_pre <= 90)) (PreH3 : (ch_pre >= 65)) (PreH4 : (0 <= ch_pre)) (PreH5 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_10 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 73)) (PreH2 : (ch_pre <> 69)) (PreH3 : (ch_pre <> 65)) (PreH4 : (ch_pre <= 90)) (PreH5 : (ch_pre >= 65)) (PreH6 : (0 <= ch_pre)) (PreH7 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_11 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 85)) (PreH2 : (ch_pre <> 79)) (PreH3 : (ch_pre <> 73)) (PreH4 : (ch_pre <> 69)) (PreH5 : (ch_pre <> 65)) (PreH6 : (ch_pre <= 90)) (PreH7 : (ch_pre >= 65)) (PreH8 : (0 <= ch_pre)) (PreH9 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_12 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 101)) (PreH2 : (ch_pre <> 97)) (PreH3 : (ch_pre <> 85)) (PreH4 : (ch_pre <> 79)) (PreH5 : (ch_pre <> 73)) (PreH6 : (ch_pre <> 69)) (PreH7 : (ch_pre <> 65)) (PreH8 : (ch_pre <= 122)) (PreH9 : (ch_pre >= 97)) (PreH10 : (ch_pre > 90)) (PreH11 : (ch_pre >= 65)) (PreH12 : (0 <= ch_pre)) (PreH13 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_13 := 
forall (ch_pre: Z) (PreH1 : (ch_pre = 111)) (PreH2 : (ch_pre <> 105)) (PreH3 : (ch_pre <> 101)) (PreH4 : (ch_pre <> 97)) (PreH5 : (ch_pre <> 85)) (PreH6 : (ch_pre <> 79)) (PreH7 : (ch_pre <> 73)) (PreH8 : (ch_pre <> 69)) (PreH9 : (ch_pre <> 65)) (PreH10 : (ch_pre <= 122)) (PreH11 : (ch_pre >= 97)) (PreH12 : (ch_pre > 90)) (PreH13 : (ch_pre >= 65)) (PreH14 : (0 <= ch_pre)) (PreH15 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_14 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 90)) (PreH12 : (ch_pre >= 65)) (PreH13 : (0 <= ch_pre)) (PreH14 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

Definition is_consonant_char_return_wit_15 := 
forall (ch_pre: Z) (PreH1 : (ch_pre <> 117)) (PreH2 : (ch_pre <> 111)) (PreH3 : (ch_pre <> 105)) (PreH4 : (ch_pre <> 101)) (PreH5 : (ch_pre <> 97)) (PreH6 : (ch_pre <> 85)) (PreH7 : (ch_pre <> 79)) (PreH8 : (ch_pre <> 73)) (PreH9 : (ch_pre <> 69)) (PreH10 : (ch_pre <> 65)) (PreH11 : (ch_pre <= 122)) (PreH12 : (ch_pre >= 97)) (PreH13 : (ch_pre > 90)) (PreH14 : (ch_pre >= 65)) (PreH15 : (0 <= ch_pre)) (PreH16 : (ch_pre <= 127)) ,
  TT && emp 
|--
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 0) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = false) ”
  &&  emp)
  ||
  (“ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((is_consonant_z_117 (ch_pre)) = true) ”
  &&  emp)
.

(*----- Function select_words -----*)

Definition select_words_safety_wit_1 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_2 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  ((( &( "start" ) )) # Int  |->_)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_3 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  ((( &( "out_size" ) )) # Int  |->_)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_4 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  ((( &( "numc" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_5 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (0 <= need_pre)) (PreH5 : (need_pre < INT_MAX)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_select_words_input_117 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_117_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_6 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (0 <= need_pre)) (PreH5 : (need_pre < INT_MAX)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_select_words_input_117 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_117_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition select_words_safety_wit_7 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (0 <= need_pre)) (PreH5 : (need_pre < INT_MAX)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_select_words_input_117 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_117_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_8 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
  ((( &( "ch" ) )) # Int  |->_)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_9 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
  ((( &( "len" ) )) # Int  |->_)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_10 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
  ((( &( "addc" ) )) # Int  |->_)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_11 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
  ((( &( "w" ) )) # Ptr  |->_)
  **  ((( &( "addc" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_12 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "w" ) )) # Ptr  |-> 0)
  **  ((( &( "addc" ) )) # Int  |-> 0)
  **  ((( &( "len" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> 0)
  **  ((( &( "data" ) )) # Ptr  |-> retval_3)
  **  (PtrArray.undef_full retval_3 (retval + 1 ) )
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_13 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i < n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (0 <= numc)) (PreH14 : (numc <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (0 <= addc)) (PreH20 : (addc <= 1)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition select_words_safety_wit_14 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= numc)) (PreH15 : (numc <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (0 <= addc)) (PreH21 : (addc <= 1)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_15 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((i - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - start )) ”
.

Definition select_words_safety_wit_16 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i - start ) + 1 )) ”
.

Definition select_words_safety_wit_17 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_18 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= numc)) (PreH19 : (numc <= i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_19 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_space_z_117 (ch)) = true)) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH33 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition select_words_safety_wit_20 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH34 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH35 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition select_words_safety_wit_21 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_space_z_117 (ch)) = true)) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH33 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_22 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition select_words_safety_wit_23 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_24 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_25 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
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
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_26 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_27 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_28 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_29 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_30 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_31 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_32 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH2 : (i < n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= numc)) (PreH15 : (numc <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (0 <= addc)) (PreH21 : (addc <= 1)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_33 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_34 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (start < 0)) (PreH7 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (out_size = (Zlength (output_rows)))) (PreH17 : ((Zlength (output_ptrs)) = out_size)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= numc)) (PreH21 : (numc <= i)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= len)) (PreH25 : (len < INT_MAX)) (PreH26 : (0 <= addc)) (PreH27 : (addc <= 1)) (PreH28 : (0 <= need_pre)) (PreH29 : (need_pre < INT_MAX)) (PreH30 : (valid_string str_l )) (PreH31 : (all_ascii str_l )) (PreH32 : (valid_select_words_input_117 str_l )) (PreH33 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH34 : (problem_117_pre_z str_l )) (PreH35 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_35 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (start < 0)) (PreH7 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (out_size = (Zlength (output_rows)))) (PreH17 : ((Zlength (output_ptrs)) = out_size)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= numc)) (PreH21 : (numc <= i)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= len)) (PreH25 : (len < INT_MAX)) (PreH26 : (0 <= addc)) (PreH27 : (addc <= 1)) (PreH28 : (0 <= need_pre)) (PreH29 : (need_pre < INT_MAX)) (PreH30 : (valid_string str_l )) (PreH31 : (all_ascii str_l )) (PreH32 : (valid_select_words_input_117 str_l )) (PreH33 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH34 : (problem_117_pre_z str_l )) (PreH35 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_36 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 0)) (PreH4 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (start >= 0)) (PreH7 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (out_size = (Zlength (output_rows)))) (PreH17 : ((Zlength (output_ptrs)) = out_size)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= numc)) (PreH21 : (numc <= i)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= len)) (PreH25 : (len < INT_MAX)) (PreH26 : (0 <= addc)) (PreH27 : (addc <= 1)) (PreH28 : (0 <= need_pre)) (PreH29 : (need_pre < INT_MAX)) (PreH30 : (valid_string str_l )) (PreH31 : (all_ascii str_l )) (PreH32 : (valid_select_words_input_117 str_l )) (PreH33 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH34 : (problem_117_pre_z str_l )) (PreH35 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_37 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval <= 1)) (PreH3 : (retval = 1)) (PreH4 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH5 : (0 <= ((string_length (str_l)) + 1 ))) (PreH6 : (start >= 0)) (PreH7 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH8 : (i < n)) (PreH9 : (0 <= i)) (PreH10 : (i <= n)) (PreH11 : (n = (string_length (str_l)))) (PreH12 : (out <> 0)) (PreH13 : (data <> 0)) (PreH14 : (0 <= out_size)) (PreH15 : (out_size <= i)) (PreH16 : (out_size = (Zlength (output_rows)))) (PreH17 : ((Zlength (output_ptrs)) = out_size)) (PreH18 : ((-1) <= start)) (PreH19 : (start < i)) (PreH20 : (0 <= numc)) (PreH21 : (numc <= i)) (PreH22 : (0 <= ch)) (PreH23 : (ch <= 127)) (PreH24 : (0 <= len)) (PreH25 : (len < INT_MAX)) (PreH26 : (0 <= addc)) (PreH27 : (addc <= 1)) (PreH28 : (0 <= need_pre)) (PreH29 : (need_pre < INT_MAX)) (PreH30 : (valid_string str_l )) (PreH31 : (all_ascii str_l )) (PreH32 : (valid_select_words_input_117 str_l )) (PreH33 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH34 : (problem_117_pre_z str_l )) (PreH35 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_38 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ False ”
.

Definition select_words_safety_wit_39 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ False ”
.

Definition select_words_safety_wit_40 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ False ”
.

Definition select_words_safety_wit_41 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ False ”
.

Definition select_words_safety_wit_42 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition select_words_safety_wit_43 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows)))) (PreH18 : ((Zlength (output_ptrs)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> retval)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((numc + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numc + 1 )) ”
.

Definition select_words_safety_wit_44 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (numc = 0)) (PreH13 : ((is_space_z_117 (ch)) = true)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (0 <= addc)) (PreH19 : (addc <= 1)) (PreH20 : (0 <= need_pre)) (PreH21 : (need_pre < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_select_words_input_117 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_117_pre_z str_l )) (PreH27 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition select_words_safety_wit_45 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (numc = 0)) (PreH12 : ((is_space_z_117 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (0 <= addc)) (PreH18 : (addc <= 1)) (PreH19 : (0 <= need_pre)) (PreH20 : (need_pre < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_select_words_input_117 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_117_pre_z str_l )) (PreH26 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition select_words_safety_wit_46 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (numc = 0)) (PreH12 : ((is_space_z_117 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (0 <= addc)) (PreH18 : (addc <= 1)) (PreH19 : (0 <= need_pre)) (PreH20 : (need_pre < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_select_words_input_117 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_117_pre_z str_l )) (PreH26 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition select_words_safety_wit_47 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows)))) (PreH9 : ((Zlength (output_ptrs)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (0 <= numc)) (PreH13 : (numc <= (i + 1 ))) (PreH14 : ((is_space_z_117 (ch)) = false)) (PreH15 : (numc = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre)))))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (0 <= addc)) (PreH21 : (addc <= 1)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition select_words_safety_wit_48 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (i >= n)) (PreH2 : (0 <= i)) (PreH3 : (i <= n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : ((-1) <= start)) (PreH12 : (start < i)) (PreH13 : (0 <= numc)) (PreH14 : (numc <= i)) (PreH15 : (0 <= ch)) (PreH16 : (ch <= 127)) (PreH17 : (0 <= len)) (PreH18 : (len < INT_MAX)) (PreH19 : (0 <= addc)) (PreH20 : (addc <= 1)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_49 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((n - start ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n - start )) ”
.

Definition select_words_safety_wit_50 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((n - start ) + 1 )) ”
.

Definition select_words_safety_wit_51 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_52 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : (i >= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= numc)) (PreH18 : (numc <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
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
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_53 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= addc)) (PreH9 : (addc <= 1)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH29 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ ((start + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (start + k )) ”
.

Definition select_words_safety_wit_54 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= addc)) (PreH10 : (addc <= 1)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= n)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : (0 <= start)) (PreH16 : (start < n)) (PreH17 : (len = (n - start ))) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH30 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH31 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition select_words_safety_wit_55 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= addc)) (PreH9 : (addc <= 1)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH29 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
  **  (CharArray.undef_seg w k (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_56 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((out_size + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out_size + 1 )) ”
.

Definition select_words_safety_wit_57 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_58 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_59 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows)))) (PreH15 : ((Zlength (output_ptrs)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "out_size" ) )) # Int  |-> (out_size + 1 ))
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_safety_wit_60 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition select_words_safety_wit_61 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition select_words_safety_wit_62 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition select_words_entail_wit_1 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l 0 (-1) 0 need_pre output_rows ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_3)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg retval_3 0 0 output_ptrs )
  **  (PtrArray.undef_seg retval_3 0 (retval + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (retval_3: Z) (PreH1 : (retval_3 <> 0)) (PreH2 : (retval_2 <> 0)) (PreH3 : (retval = (string_length (str_l)))) (PreH4 : (0 <= ((string_length (str_l)) + 1 ))) (PreH5 : (0 <= need_pre)) (PreH6 : (need_pre < INT_MAX)) (PreH7 : (valid_string str_l )) (PreH8 : (all_ascii str_l )) (PreH9 : (valid_select_words_input_117 str_l )) (PreH10 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH11 : (problem_117_pre_z str_l )) ,
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l 0 (-1) 0 need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 (@nil Z) output_rows )
).

Definition select_words_entail_wit_2 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= numc)) (PreH19 : (numc <= i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = (i - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_117 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((i - start ) + 1 ) )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH6 : (i < n)) (PreH7 : (0 <= i)) (PreH8 : (i <= n)) (PreH9 : (n = (string_length (str_l)))) (PreH10 : (out <> 0)) (PreH11 : (data <> 0)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= i)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : ((-1) <= start)) (PreH17 : (start < i)) (PreH18 : (0 <= numc)) (PreH19 : (numc <= i)) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= len)) (PreH23 : (len < INT_MAX)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((word_payload_117 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
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
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i - start )) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = (i - start )) ”
  &&  (CharArray.undef_full retval ((i - start ) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_3 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH34 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH35 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_117 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH34 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH35 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) = (word_payload_117 (str_l) (start) ((start + (k + 1 ) )))) ” 
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_4 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH20 : (0 <= ch)) (PreH21 : (ch <= 127)) (PreH22 : (0 <= k)) (PreH23 : (k <= len)) (PreH24 : (0 <= addc)) (PreH25 : (addc <= 1)) (PreH26 : (0 <= need_pre)) (PreH27 : (need_pre < INT_MAX)) (PreH28 : (valid_string str_l )) (PreH29 : (all_ascii str_l )) (PreH30 : (valid_select_words_input_117 str_l )) (PreH31 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH32 : (problem_117_pre_z str_l )) (PreH33 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH34 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH35 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (0 <= i)) (PreH5 : (i < n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (w <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < i)) (PreH16 : (len = (i - start ))) (PreH17 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH18 : ((is_space_z_117 (ch)) = true)) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH21 : (0 <= ch)) (PreH22 : (ch <= 127)) (PreH23 : (0 <= k)) (PreH24 : (k <= len)) (PreH25 : (0 <= addc)) (PreH26 : (addc <= 1)) (PreH27 : (0 <= need_pre)) (PreH28 : (need_pre < INT_MAX)) (PreH29 : (valid_string str_l )) (PreH30 : (all_ascii str_l )) (PreH31 : (valid_select_words_input_117 str_l )) (PreH32 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH33 : (problem_117_pre_z str_l )) (PreH34 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH35 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH36 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
).

Definition select_words_entail_wit_5 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
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
  &&  “ (0 = 0) ” 
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (0 <= (len + 1 ))) (PreH3 : (0 <= i)) (PreH4 : (i < n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (w <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : (0 <= start)) (PreH14 : (start < i)) (PreH15 : (len = (i - start ))) (PreH16 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH17 : ((is_space_z_117 (ch)) = true)) (PreH18 : (numc = need_pre)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) output_rows )
).

Definition select_words_entail_wit_6 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (numc <> need_pre)) (PreH3 : (start >= 0)) (PreH4 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH5 : (i < n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= numc)) (PreH18 : (numc <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_7 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = true) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) (-1) 0 need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_8_1 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ (numc = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ (numc = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_8_2 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ (0 = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) i 0 need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 0)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = false)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ (0 = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) i 0 need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_8_3 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= (numc + 1 )) ” 
  &&  “ ((numc + 1 ) <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ ((numc + 1 ) = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start (numc + 1 ) need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start >= 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= (numc + 1 )) ” 
  &&  “ ((numc + 1 ) <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ ((numc + 1 ) = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start (numc + 1 ) need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_8_4 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ ((0 + 1 ) = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) i (0 + 1 ) need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= retval)) (PreH3 : (retval <= 1)) (PreH4 : (retval = 1)) (PreH5 : ((is_consonant_z_117 ((Znth i (c_string (str_l)) 0))) = true)) (PreH6 : (0 <= ((string_length (str_l)) + 1 ))) (PreH7 : (start < 0)) (PreH8 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH9 : (i < n)) (PreH10 : (0 <= i)) (PreH11 : (i <= n)) (PreH12 : (n = (string_length (str_l)))) (PreH13 : (out <> 0)) (PreH14 : (data <> 0)) (PreH15 : (0 <= out_size)) (PreH16 : (out_size <= i)) (PreH17 : (out_size = (Zlength (output_rows_2)))) (PreH18 : ((Zlength (output_ptrs_2)) = out_size)) (PreH19 : ((-1) <= start)) (PreH20 : (start < i)) (PreH21 : (0 <= numc)) (PreH22 : (numc <= i)) (PreH23 : (0 <= ch)) (PreH24 : (ch <= 127)) (PreH25 : (0 <= len)) (PreH26 : (len < INT_MAX)) (PreH27 : (0 <= addc)) (PreH28 : (addc <= 1)) (PreH29 : (0 <= need_pre)) (PreH30 : (need_pre < INT_MAX)) (PreH31 : (valid_string str_l )) (PreH32 : (all_ascii str_l )) (PreH33 : (valid_select_words_input_117 str_l )) (PreH34 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH35 : (problem_117_pre_z str_l )) (PreH36 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= (0 + 1 )) ” 
  &&  “ ((0 + 1 ) <= (i + 1 )) ” 
  &&  “ ((is_space_z_117 ((Znth i (c_string (str_l)) 0))) = false) ” 
  &&  “ ((0 + 1 ) = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre))))) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) i (0 + 1 ) need_pre output_rows ) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_9_1 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= (i + 1 ))) (PreH9 : (out_size = (Zlength (output_rows_2)))) (PreH10 : ((Zlength (output_ptrs_2)) = out_size)) (PreH11 : (start = (-1))) (PreH12 : (numc = 0)) (PreH13 : ((is_space_z_117 (ch)) = true)) (PreH14 : (0 <= ch)) (PreH15 : (ch <= 127)) (PreH16 : (0 <= len)) (PreH17 : (len < INT_MAX)) (PreH18 : (0 <= addc)) (PreH19 : (addc <= 1)) (PreH20 : (0 <= need_pre)) (PreH21 : (need_pre < INT_MAX)) (PreH22 : (valid_string str_l )) (PreH23 : (all_ascii str_l )) (PreH24 : (valid_select_words_input_117 str_l )) (PreH25 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH26 : (problem_117_pre_z str_l )) (PreH27 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_entail_wit_9_2 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (numc = 0)) (PreH12 : ((is_space_z_117 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (0 <= addc)) (PreH18 : (addc <= 1)) (PreH19 : (0 <= need_pre)) (PreH20 : (need_pre < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_select_words_input_117 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_117_pre_z str_l )) (PreH26 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_entail_wit_9_3 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (start = (-1))) (PreH11 : (numc = 0)) (PreH12 : ((is_space_z_117 (ch)) = true)) (PreH13 : (0 <= ch)) (PreH14 : (ch <= 127)) (PreH15 : (0 <= len)) (PreH16 : (len < INT_MAX)) (PreH17 : (0 <= addc)) (PreH18 : (addc <= 1)) (PreH19 : (0 <= need_pre)) (PreH20 : (need_pre < INT_MAX)) (PreH21 : (valid_string str_l )) (PreH22 : (all_ascii str_l )) (PreH23 : (valid_select_words_input_117 str_l )) (PreH24 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH25 : (problem_117_pre_z str_l )) (PreH26 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_entail_wit_9_4 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (out_size: Z) (start: Z) (numc: Z) (ch: Z) (len: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (0 <= out_size)) (PreH7 : (out_size <= i)) (PreH8 : (out_size = (Zlength (output_rows_2)))) (PreH9 : ((Zlength (output_ptrs_2)) = out_size)) (PreH10 : (0 <= start)) (PreH11 : (start <= i)) (PreH12 : (0 <= numc)) (PreH13 : (numc <= (i + 1 ))) (PreH14 : ((is_space_z_117 (ch)) = false)) (PreH15 : (numc = (count_consonants_z_117 ((select_current_117 (str_l) ((i + 1 )) (need_pre)))))) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (0 <= addc)) (PreH21 : (addc <= 1)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= (i + 1 )) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l (i + 1 ) start numc need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_entail_wit_10 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : (i >= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= numc)) (PreH18 : (numc <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ ((n - start ) = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n - start )) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = (n - start )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full retval 0 (word_payload_117 (str_l) (start) ((start + 0 ))) )
  **  (CharArray.undef_seg retval 0 ((n - start ) + 1 ) )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (numc = need_pre)) (PreH4 : (start >= 0)) (PreH5 : (i >= n)) (PreH6 : (0 <= i)) (PreH7 : (i <= n)) (PreH8 : (n = (string_length (str_l)))) (PreH9 : (out <> 0)) (PreH10 : (data <> 0)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= i)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : ((-1) <= start)) (PreH16 : (start < i)) (PreH17 : (0 <= numc)) (PreH18 : (numc <= i)) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= len)) (PreH22 : (len < INT_MAX)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((word_payload_117 (str_l) (start) ((start + 0 ))) = (@nil Z)) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (n - start )) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = (n - start )) ”
  &&  (CharArray.undef_full retval ((n - start ) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_11 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= addc)) (PreH10 : (addc <= 1)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= n)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : (0 <= start)) (PreH16 : (start < n)) (PreH17 : (len = (n - start ))) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH30 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH31 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (k + 1 ) (word_payload_117 (str_l) (start) ((start + (k + 1 ) ))) )
  **  (CharArray.undef_seg w (k + 1 ) (len + 1 ) )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k < len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= addc)) (PreH10 : (addc <= 1)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= n)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : (0 <= start)) (PreH16 : (start < n)) (PreH17 : (len = (n - start ))) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH30 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH31 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_rows: (@list (@list Z))) ,
  “ ((app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons ((Znth (start + k ) (c_string (str_l)) 0)) ((@nil Z))))) = (word_payload_117 (str_l) (start) ((start + (k + 1 ) )))) ” 
  &&  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (w <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs_2)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= len) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 output_rows )
).

Definition select_words_entail_wit_12_1 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : (i >= n)) (PreH3 : (0 <= i)) (PreH4 : (i <= n)) (PreH5 : (n = (string_length (str_l)))) (PreH6 : (out <> 0)) (PreH7 : (data <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows_2)))) (PreH11 : ((Zlength (output_ptrs_2)) = out_size)) (PreH12 : ((-1) <= start)) (PreH13 : (start < i)) (PreH14 : (0 <= numc)) (PreH15 : (numc <= i)) (PreH16 : (0 <= ch)) (PreH17 : (ch <= 127)) (PreH18 : (0 <= len)) (PreH19 : (len < INT_MAX)) (PreH20 : (0 <= addc)) (PreH21 : (addc <= 1)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (start = (-1)) ” 
  &&  “ (numc = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (output_rows = (select_output_rows_117 (str_l) (need_pre))) ” 
  &&  “ (problem_117_spec_z str_l need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ” 
  &&  “ (numc = 0) ” 
  &&  “ (out_size = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 (select_output_rows_117 (str_l) (need_pre)) )
).

Definition select_words_entail_wit_12_1_split_goal_1 := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ”
.

Definition select_words_entail_wit_12_1_split_goal_2 := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (numc = 0) ”
.

Definition select_words_entail_wit_12_1_split_goal_3 := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (out_size = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
.

Definition select_words_entail_wit_12_1_split_goal_spatial := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (start < 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  (select_words_rows_heap_117 output_ptrs_2 (select_output_rows_117 (str_l) (need_pre)) )
.

Definition select_words_entail_wit_12_2 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc <> need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows_2)))) (PreH12 : ((Zlength (output_ptrs_2)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (output_rows = (select_output_rows_117 (str_l) (need_pre))) ” 
  &&  “ (problem_117_spec_z str_l need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (numc <> need_pre)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ” 
  &&  “ (out_size = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
  &&  (select_words_rows_heap_117 output_ptrs_2 (select_output_rows_117 (str_l) (need_pre)) )
).

Definition select_words_entail_wit_12_2_split_goal_1 := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (numc <> need_pre)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ”
.

Definition select_words_entail_wit_12_2_split_goal_2 := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (numc <> need_pre)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (out_size = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
.

Definition select_words_entail_wit_12_2_split_goal_spatial := 
forall (need_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (numc <> need_pre)) (PreH3 : (start >= 0)) (PreH4 : (i >= n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows_2 )) ,
  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  (select_words_rows_heap_117 output_ptrs_2 (select_output_rows_117 (str_l) (need_pre)) )
.

Definition select_words_entail_wit_12_3 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (PtrArray.seg data 0 (out_size + 1 ) (app (output_ptrs_2) ((cons (w) ((@nil Z))))) )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (n = (string_length (str_l))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ ((out_size + 1 ) = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = (out_size + 1 )) ” 
  &&  “ ((-1) = (-1)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (output_rows = (select_output_rows_117 (str_l) (need_pre))) ” 
  &&  “ (problem_117_spec_z str_l need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (out_size + 1 ))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (out_size + 1 ) output_ptrs )
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ” 
  &&  “ ((Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z))))))) = (out_size + 1 )) ” 
  &&  “ ((out_size + 1 ) = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
  &&  (select_words_rows_heap_117 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) (select_output_rows_117 (str_l) (need_pre)) )
).

Definition select_words_entail_wit_12_3_split_goal_1 := 
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ (problem_117_spec_z str_l need_pre (select_output_rows_117 (str_l) (need_pre)) ) ”
.

Definition select_words_entail_wit_12_3_split_goal_2 := 
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ ((Zlength ((app (output_ptrs_2) ((cons (w) ((@nil Z))))))) = (out_size + 1 )) ”
.

Definition select_words_entail_wit_12_3_split_goal_3 := 
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  “ ((out_size + 1 ) = (Zlength ((select_output_rows_117 (str_l) (need_pre))))) ”
.

Definition select_words_entail_wit_12_3_split_goal_spatial := 
forall (need_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs_2: (@list Z)) (output_rows_2: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= (k + 1 ))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (k >= len)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= ch)) (PreH9 : (ch <= 127)) (PreH10 : (0 <= addc)) (PreH11 : (addc <= 1)) (PreH12 : (0 <= out_size)) (PreH13 : (out_size <= n)) (PreH14 : (out_size = (Zlength (output_rows_2)))) (PreH15 : ((Zlength (output_ptrs_2)) = out_size)) (PreH16 : (0 <= start)) (PreH17 : (start < n)) (PreH18 : (len = (n - start ))) (PreH19 : (numc = need_pre)) (PreH20 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l n start numc need_pre output_rows_2 )) (PreH31 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH32 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  (select_words_rows_heap_117 (app (output_ptrs_2) ((cons (w) ((@nil Z))))) (select_output_rows_117 (str_l) (need_pre)) )
.

Definition select_words_return_wit_1 := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (addc: Z) (out_size: Z) (start: Z) (numc: Z) (PreH1 : (n = (string_length (str_l)))) (PreH2 : (out <> 0)) (PreH3 : (data_2 <> 0)) (PreH4 : (0 <= ch)) (PreH5 : (ch <= 127)) (PreH6 : (0 <= len)) (PreH7 : (len < INT_MAX)) (PreH8 : (0 <= addc)) (PreH9 : (addc <= 1)) (PreH10 : (0 <= need_pre)) (PreH11 : (need_pre < INT_MAX)) (PreH12 : (out_size = (Zlength (output_rows_2)))) (PreH13 : ((Zlength (output_ptrs_2)) = out_size)) (PreH14 : (start = (-1))) (PreH15 : (numc = 0)) (PreH16 : (valid_string str_l )) (PreH17 : (all_ascii str_l )) (PreH18 : (valid_select_words_input_117 str_l )) (PreH19 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH20 : (problem_117_pre_z str_l )) (PreH21 : (output_rows_2 = (select_output_rows_117 (str_l) (need_pre)))) (PreH22 : (problem_117_spec_z str_l need_pre output_rows_2 )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z)))  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (problem_117_spec_z str_l need_pre output_rows ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (Zlength (output_rows)))
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
) \/
(
forall (need_pre: Z) (str_l: (@list Z)) (output_rows_2: (@list (@list Z))) (output_ptrs_2: (@list Z)) (n: Z) (out: Z) (data_2: Z) (ch: Z) (len: Z) (addc: Z) (out_size: Z) (start: Z) (numc: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data_2 <> 0)) (PreH5 : (0 <= ch)) (PreH6 : (ch <= 127)) (PreH7 : (0 <= len)) (PreH8 : (len < INT_MAX)) (PreH9 : (0 <= addc)) (PreH10 : (addc <= 1)) (PreH11 : (0 <= need_pre)) (PreH12 : (need_pre < INT_MAX)) (PreH13 : (out_size = (Zlength (output_rows_2)))) (PreH14 : ((Zlength (output_ptrs_2)) = out_size)) (PreH15 : (start = (-1))) (PreH16 : (numc = 0)) (PreH17 : (valid_string str_l )) (PreH18 : (all_ascii str_l )) (PreH19 : (valid_select_words_input_117 str_l )) (PreH20 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH21 : (problem_117_pre_z str_l )) (PreH22 : (output_rows_2 = (select_output_rows_117 (str_l) (need_pre)))) (PreH23 : (problem_117_spec_z str_l need_pre output_rows_2 )) ,
  (PtrArray.seg data_2 0 out_size output_ptrs_2 )
  **  (PtrArray.undef_seg data_2 out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs_2 output_rows_2 )
|--
  EX (output_ptrs: (@list Z))  (output_rows: (@list (@list Z))) ,
  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ ((Zlength (output_rows)) <= ((string_length (str_l)) + 1 )) ” 
  &&  “ ((Zlength (output_ptrs)) = (Zlength (output_rows))) ” 
  &&  “ (problem_117_spec_z str_l need_pre output_rows ) ”
  &&  (PtrArray.seg data_2 0 (Zlength (output_rows)) output_ptrs )
  **  (PtrArray.undef_seg data_2 (Zlength (output_rows)) ((string_length (str_l)) + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
).

Definition select_words_partial_solve_wit_1_pure := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ”
.

Definition select_words_partial_solve_wit_1_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (PreH1 : (0 <= need_pre)) (PreH2 : (need_pre < INT_MAX)) (PreH3 : (valid_string str_l )) (PreH4 : (all_ascii str_l )) (PreH5 : (valid_select_words_input_117 str_l )) (PreH6 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH7 : (problem_117_pre_z str_l )) ,
  (store_string s_pre str_l )
|--
  “ (valid_string str_l ) ” 
  &&  “ ((string_length (str_l)) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ”
  &&  (store_string s_pre str_l )
.

Definition select_words_partial_solve_wit_1 := select_words_partial_solve_wit_1_pure -> select_words_partial_solve_wit_1_aux.

Definition select_words_partial_solve_wit_2 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (PreH1 : (retval = (string_length (str_l)))) (PreH2 : (0 <= ((string_length (str_l)) + 1 ))) (PreH3 : (0 <= need_pre)) (PreH4 : (need_pre < INT_MAX)) (PreH5 : (valid_string str_l )) (PreH6 : (all_ascii str_l )) (PreH7 : (valid_select_words_input_117 str_l )) (PreH8 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH9 : (problem_117_pre_z str_l )) ,
  (store_string s_pre str_l )
|--
  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition select_words_partial_solve_wit_3_pure := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (0 <= need_pre)) (PreH5 : (need_pre < INT_MAX)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_select_words_input_117 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_117_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "out_size" ) )) # Int  |-> 0)
  **  ((( &( "start" ) )) # Int  |-> (-1))
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ”
.

Definition select_words_partial_solve_wit_3_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (retval: Z) (retval_2: Z) (PreH1 : (retval_2 <> 0)) (PreH2 : (retval = (string_length (str_l)))) (PreH3 : (0 <= ((string_length (str_l)) + 1 ))) (PreH4 : (0 <= need_pre)) (PreH5 : (need_pre < INT_MAX)) (PreH6 : (valid_string str_l )) (PreH7 : (all_ascii str_l )) (PreH8 : (valid_select_words_input_117 str_l )) (PreH9 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH10 : (problem_117_pre_z str_l )) ,
  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
|--
  “ (0 <= (retval + 1 )) ” 
  &&  “ ((retval + 1 ) < INT_MAX) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval = (string_length (str_l))) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ”
  &&  ((&((retval_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 0)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
.

Definition select_words_partial_solve_wit_3 := select_words_partial_solve_wit_3_pure -> select_words_partial_solve_wit_3_aux.

Definition select_words_partial_solve_wit_4_pure := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> (i - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ”
.

Definition select_words_partial_solve_wit_4_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : ((Znth i (c_string (str_l)) 0) = 32)) (PreH4 : (i < n)) (PreH5 : (0 <= i)) (PreH6 : (i <= n)) (PreH7 : (n = (string_length (str_l)))) (PreH8 : (out <> 0)) (PreH9 : (data <> 0)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= i)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : ((-1) <= start)) (PreH15 : (start < i)) (PreH16 : (0 <= numc)) (PreH17 : (numc <= i)) (PreH18 : (0 <= ch)) (PreH19 : (ch <= 127)) (PreH20 : (0 <= len)) (PreH21 : (len < INT_MAX)) (PreH22 : (0 <= addc)) (PreH23 : (addc <= 1)) (PreH24 : (0 <= need_pre)) (PreH25 : (need_pre < INT_MAX)) (PreH26 : (valid_string str_l )) (PreH27 : (all_ascii str_l )) (PreH28 : (valid_select_words_input_117 str_l )) (PreH29 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH30 : (problem_117_pre_z str_l )) (PreH31 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((i - start ) + 1 ) > 0) ” 
  &&  “ (((i - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (numc = need_pre) ” 
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_partial_solve_wit_4 := select_words_partial_solve_wit_4_pure -> select_words_partial_solve_wit_4_aux.

Definition select_words_partial_solve_wit_5 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k < len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_space_z_117 (ch)) = true)) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH33 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
.

Definition select_words_partial_solve_wit_6 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (k: Z) (numc: Z) (ch: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (k >= len)) (PreH2 : (0 <= i)) (PreH3 : (i < n)) (PreH4 : (n = (string_length (str_l)))) (PreH5 : (out <> 0)) (PreH6 : (data <> 0)) (PreH7 : (w <> 0)) (PreH8 : (0 <= out_size)) (PreH9 : (out_size <= i)) (PreH10 : (out_size = (Zlength (output_rows)))) (PreH11 : ((Zlength (output_ptrs)) = out_size)) (PreH12 : (0 <= start)) (PreH13 : (start < i)) (PreH14 : (len = (i - start ))) (PreH15 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH16 : ((is_space_z_117 (ch)) = true)) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i)))))) (PreH19 : (0 <= ch)) (PreH20 : (ch <= 127)) (PreH21 : (0 <= k)) (PreH22 : (k <= len)) (PreH23 : (0 <= addc)) (PreH24 : (addc <= 1)) (PreH25 : (0 <= need_pre)) (PreH26 : (need_pre < INT_MAX)) (PreH27 : (valid_string str_l )) (PreH28 : (all_ascii str_l )) (PreH29 : (valid_select_words_input_117 str_l )) (PreH30 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH31 : (problem_117_pre_z str_l )) (PreH32 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH33 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) (PreH34 : ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (i))))) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (i)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
.

Definition select_words_partial_solve_wit_7 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (output_rows: (@list (@list Z))) (output_ptrs: (@list Z)) (i: Z) (n: Z) (out: Z) (data: Z) (w: Z) (out_size: Z) (start: Z) (len: Z) (ch: Z) (numc: Z) (addc: Z) (PreH1 : (0 <= i)) (PreH2 : (i < n)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= out_size)) (PreH8 : (out_size <= i)) (PreH9 : (out_size = (Zlength (output_rows)))) (PreH10 : ((Zlength (output_ptrs)) = out_size)) (PreH11 : (0 <= start)) (PreH12 : (start < i)) (PreH13 : (len = (i - start ))) (PreH14 : (ch = (Znth (i) ((c_string (str_l))) (0)))) (PreH15 : ((is_space_z_117 (ch)) = true)) (PreH16 : (numc = need_pre)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= addc)) (PreH20 : (addc <= 1)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l i start numc need_pre output_rows )) (PreH29 : ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i)))) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
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
  &&  “ ((is_space_z_117 (ch)) = true) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (i) (need_pre)) = (word_payload_117 (str_l) (start) (i))) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w (len + 1 ) (word_row_117 (str_l) (start) (i)) )
.

Definition select_words_partial_solve_wit_8_pure := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
) \/
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (0 <= INT_MAX)) (PreH6 : (out_size <= INT_MAX)) (PreH7 : (n <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (need_pre >= INT_MIN)) (PreH10 : (addc >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH13 : (0 >= INT_MIN)) (PreH14 : (out_size >= INT_MIN)) (PreH15 : (n >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((string_length (str_l)) + 1 ))) (PreH18 : (start < 0)) (PreH19 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH20 : (i < n)) (PreH21 : (0 <= i)) (PreH22 : (i <= n)) (PreH23 : (n = (string_length (str_l)))) (PreH24 : (out <> 0)) (PreH25 : (data <> 0)) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= i)) (PreH28 : (out_size = (Zlength (output_rows)))) (PreH29 : ((Zlength (output_ptrs)) = out_size)) (PreH30 : ((-1) <= start)) (PreH31 : (start < i)) (PreH32 : (0 <= numc)) (PreH33 : (numc <= i)) (PreH34 : (0 <= ch)) (PreH35 : (ch <= 127)) (PreH36 : (0 <= len)) (PreH37 : (len < INT_MAX)) (PreH38 : (0 <= addc)) (PreH39 : (addc <= 1)) (PreH40 : (0 <= need_pre)) (PreH41 : (need_pre < INT_MAX)) (PreH42 : (valid_string str_l )) (PreH43 : (all_ascii str_l )) (PreH44 : (valid_select_words_input_117 str_l )) (PreH45 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH46 : (problem_117_pre_z str_l )) (PreH47 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
).

Definition select_words_partial_solve_wit_8_pure_split_goal_1 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (0 <= INT_MAX)) (PreH6 : (out_size <= INT_MAX)) (PreH7 : (n <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (need_pre >= INT_MIN)) (PreH10 : (addc >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH13 : (0 >= INT_MIN)) (PreH14 : (out_size >= INT_MIN)) (PreH15 : (n >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((string_length (str_l)) + 1 ))) (PreH18 : (start < 0)) (PreH19 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH20 : (i < n)) (PreH21 : (0 <= i)) (PreH22 : (i <= n)) (PreH23 : (n = (string_length (str_l)))) (PreH24 : (out <> 0)) (PreH25 : (data <> 0)) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= i)) (PreH28 : (out_size = (Zlength (output_rows)))) (PreH29 : ((Zlength (output_ptrs)) = out_size)) (PreH30 : ((-1) <= start)) (PreH31 : (start < i)) (PreH32 : (0 <= numc)) (PreH33 : (numc <= i)) (PreH34 : (0 <= ch)) (PreH35 : (ch <= 127)) (PreH36 : (0 <= len)) (PreH37 : (len < INT_MAX)) (PreH38 : (0 <= addc)) (PreH39 : (addc <= 1)) (PreH40 : (0 <= need_pre)) (PreH41 : (need_pre < INT_MAX)) (PreH42 : (valid_string str_l )) (PreH43 : (all_ascii str_l )) (PreH44 : (valid_select_words_input_117 str_l )) (PreH45 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH46 : (problem_117_pre_z str_l )) (PreH47 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition select_words_partial_solve_wit_8_pure_split_goal_2 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (0 <= INT_MAX)) (PreH6 : (out_size <= INT_MAX)) (PreH7 : (n <= INT_MAX)) (PreH8 : (i <= INT_MAX)) (PreH9 : (need_pre >= INT_MIN)) (PreH10 : (addc >= INT_MIN)) (PreH11 : (len >= INT_MIN)) (PreH12 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH13 : (0 >= INT_MIN)) (PreH14 : (out_size >= INT_MIN)) (PreH15 : (n >= INT_MIN)) (PreH16 : (i >= INT_MIN)) (PreH17 : (0 <= ((string_length (str_l)) + 1 ))) (PreH18 : (start < 0)) (PreH19 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH20 : (i < n)) (PreH21 : (0 <= i)) (PreH22 : (i <= n)) (PreH23 : (n = (string_length (str_l)))) (PreH24 : (out <> 0)) (PreH25 : (data <> 0)) (PreH26 : (0 <= out_size)) (PreH27 : (out_size <= i)) (PreH28 : (out_size = (Zlength (output_rows)))) (PreH29 : ((Zlength (output_ptrs)) = out_size)) (PreH30 : ((-1) <= start)) (PreH31 : (start < i)) (PreH32 : (0 <= numc)) (PreH33 : (numc <= i)) (PreH34 : (0 <= ch)) (PreH35 : (ch <= 127)) (PreH36 : (0 <= len)) (PreH37 : (len < INT_MAX)) (PreH38 : (0 <= addc)) (PreH39 : (addc <= 1)) (PreH40 : (0 <= need_pre)) (PreH41 : (need_pre < INT_MAX)) (PreH42 : (valid_string str_l )) (PreH43 : (all_ascii str_l )) (PreH44 : (valid_select_words_input_117 str_l )) (PreH45 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH46 : (problem_117_pre_z str_l )) (PreH47 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> i)
  **  ((( &( "numc" ) )) # Int  |-> 0)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition select_words_partial_solve_wit_8_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start < 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (start < 0) ” 
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_partial_solve_wit_8 := select_words_partial_solve_wit_8_pure -> select_words_partial_solve_wit_8_aux.

Definition select_words_partial_solve_wit_9_pure := 
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
) \/
(
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (numc <= INT_MAX)) (PreH6 : (start <= INT_MAX)) (PreH7 : (out_size <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (need_pre >= INT_MIN)) (PreH11 : (addc >= INT_MIN)) (PreH12 : (len >= INT_MIN)) (PreH13 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH14 : (numc >= INT_MIN)) (PreH15 : (start >= INT_MIN)) (PreH16 : (out_size >= INT_MIN)) (PreH17 : (n >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (0 <= ((string_length (str_l)) + 1 ))) (PreH20 : (start >= 0)) (PreH21 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH22 : (i < n)) (PreH23 : (0 <= i)) (PreH24 : (i <= n)) (PreH25 : (n = (string_length (str_l)))) (PreH26 : (out <> 0)) (PreH27 : (data <> 0)) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= i)) (PreH30 : (out_size = (Zlength (output_rows)))) (PreH31 : ((Zlength (output_ptrs)) = out_size)) (PreH32 : ((-1) <= start)) (PreH33 : (start < i)) (PreH34 : (0 <= numc)) (PreH35 : (numc <= i)) (PreH36 : (0 <= ch)) (PreH37 : (ch <= 127)) (PreH38 : (0 <= len)) (PreH39 : (len < INT_MAX)) (PreH40 : (0 <= addc)) (PreH41 : (addc <= 1)) (PreH42 : (0 <= need_pre)) (PreH43 : (need_pre < INT_MAX)) (PreH44 : (valid_string str_l )) (PreH45 : (all_ascii str_l )) (PreH46 : (valid_select_words_input_117 str_l )) (PreH47 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH48 : (problem_117_pre_z str_l )) (PreH49 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
).

Definition select_words_partial_solve_wit_9_pure_split_goal_1 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (numc <= INT_MAX)) (PreH6 : (start <= INT_MAX)) (PreH7 : (out_size <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (need_pre >= INT_MIN)) (PreH11 : (addc >= INT_MIN)) (PreH12 : (len >= INT_MIN)) (PreH13 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH14 : (numc >= INT_MIN)) (PreH15 : (start >= INT_MIN)) (PreH16 : (out_size >= INT_MIN)) (PreH17 : (n >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (0 <= ((string_length (str_l)) + 1 ))) (PreH20 : (start >= 0)) (PreH21 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH22 : (i < n)) (PreH23 : (0 <= i)) (PreH24 : (i <= n)) (PreH25 : (n = (string_length (str_l)))) (PreH26 : (out <> 0)) (PreH27 : (data <> 0)) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= i)) (PreH30 : (out_size = (Zlength (output_rows)))) (PreH31 : ((Zlength (output_ptrs)) = out_size)) (PreH32 : ((-1) <= start)) (PreH33 : (start < i)) (PreH34 : (0 <= numc)) (PreH35 : (numc <= i)) (PreH36 : (0 <= ch)) (PreH37 : (ch <= 127)) (PreH38 : (0 <= len)) (PreH39 : (len < INT_MAX)) (PreH40 : (0 <= addc)) (PreH41 : (addc <= 1)) (PreH42 : (0 <= need_pre)) (PreH43 : (need_pre < INT_MAX)) (PreH44 : (valid_string str_l )) (PreH45 : (all_ascii str_l )) (PreH46 : (valid_select_words_input_117 str_l )) (PreH47 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH48 : (problem_117_pre_z str_l )) (PreH49 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (0 <= (Znth i (c_string (str_l)) 0)) ”
.

Definition select_words_partial_solve_wit_9_pure_split_goal_2 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (need_pre <= INT_MAX)) (PreH2 : (addc <= INT_MAX)) (PreH3 : (len <= INT_MAX)) (PreH4 : ((Znth i (c_string (str_l)) 0) <= INT_MAX)) (PreH5 : (numc <= INT_MAX)) (PreH6 : (start <= INT_MAX)) (PreH7 : (out_size <= INT_MAX)) (PreH8 : (n <= INT_MAX)) (PreH9 : (i <= INT_MAX)) (PreH10 : (need_pre >= INT_MIN)) (PreH11 : (addc >= INT_MIN)) (PreH12 : (len >= INT_MIN)) (PreH13 : ((Znth i (c_string (str_l)) 0) >= INT_MIN)) (PreH14 : (numc >= INT_MIN)) (PreH15 : (start >= INT_MIN)) (PreH16 : (out_size >= INT_MIN)) (PreH17 : (n >= INT_MIN)) (PreH18 : (i >= INT_MIN)) (PreH19 : (0 <= ((string_length (str_l)) + 1 ))) (PreH20 : (start >= 0)) (PreH21 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH22 : (i < n)) (PreH23 : (0 <= i)) (PreH24 : (i <= n)) (PreH25 : (n = (string_length (str_l)))) (PreH26 : (out <> 0)) (PreH27 : (data <> 0)) (PreH28 : (0 <= out_size)) (PreH29 : (out_size <= i)) (PreH30 : (out_size = (Zlength (output_rows)))) (PreH31 : ((Zlength (output_ptrs)) = out_size)) (PreH32 : ((-1) <= start)) (PreH33 : (start < i)) (PreH34 : (0 <= numc)) (PreH35 : (numc <= i)) (PreH36 : (0 <= ch)) (PreH37 : (ch <= 127)) (PreH38 : (0 <= len)) (PreH39 : (len < INT_MAX)) (PreH40 : (0 <= addc)) (PreH41 : (addc <= 1)) (PreH42 : (0 <= need_pre)) (PreH43 : (need_pre < INT_MAX)) (PreH44 : (valid_string str_l )) (PreH45 : (all_ascii str_l )) (PreH46 : (valid_select_words_input_117 str_l )) (PreH47 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH48 : (problem_117_pre_z str_l )) (PreH49 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> (Znth i (c_string (str_l)) 0))
  **  ((( &( "len" ) )) # Int  |-> len)
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ”
.

Definition select_words_partial_solve_wit_9_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (start >= 0)) (PreH2 : ((Znth i (c_string (str_l)) 0) <> 32)) (PreH3 : (i < n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ ((Znth i (c_string (str_l)) 0) <= 127) ” 
  &&  “ (0 <= (Znth i (c_string (str_l)) 0)) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (start >= 0) ” 
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_partial_solve_wit_9 := select_words_partial_solve_wit_9_pure -> select_words_partial_solve_wit_9_aux.

Definition select_words_partial_solve_wit_10_pure := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (w: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "w" ) )) # Ptr  |-> w)
  **  ((( &( "out_size" ) )) # Int  |-> out_size)
  **  ((( &( "start" ) )) # Int  |-> start)
  **  ((( &( "numc" ) )) # Int  |-> numc)
  **  ((( &( "ch" ) )) # Int  |-> ch)
  **  ((( &( "len" ) )) # Int  |-> (n - start ))
  **  ((( &( "addc" ) )) # Int  |-> addc)
  **  ((( &( "need" ) )) # Int  |-> need_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) > 0) ” 
  &&  “ (((n - start ) + 1 ) < INT_MAX) ”
.

Definition select_words_partial_solve_wit_10_aux := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (addc: Z) (len: Z) (ch: Z) (numc: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (data: Z) (out: Z) (n: Z) (i: Z) (PreH1 : (numc = need_pre)) (PreH2 : (start >= 0)) (PreH3 : (i >= n)) (PreH4 : (0 <= i)) (PreH5 : (i <= n)) (PreH6 : (n = (string_length (str_l)))) (PreH7 : (out <> 0)) (PreH8 : (data <> 0)) (PreH9 : (0 <= out_size)) (PreH10 : (out_size <= i)) (PreH11 : (out_size = (Zlength (output_rows)))) (PreH12 : ((Zlength (output_ptrs)) = out_size)) (PreH13 : ((-1) <= start)) (PreH14 : (start < i)) (PreH15 : (0 <= numc)) (PreH16 : (numc <= i)) (PreH17 : (0 <= ch)) (PreH18 : (ch <= 127)) (PreH19 : (0 <= len)) (PreH20 : (len < INT_MAX)) (PreH21 : (0 <= addc)) (PreH22 : (addc <= 1)) (PreH23 : (0 <= need_pre)) (PreH24 : (need_pre < INT_MAX)) (PreH25 : (valid_string str_l )) (PreH26 : (all_ascii str_l )) (PreH27 : (valid_select_words_input_117 str_l )) (PreH28 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH29 : (problem_117_pre_z str_l )) (PreH30 : (select_scan_state_117 str_l i start numc need_pre output_rows )) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
|--
  “ (((n - start ) + 1 ) > 0) ” 
  &&  “ (((n - start ) + 1 ) < INT_MAX) ” 
  &&  “ (0 <= ((string_length (str_l)) + 1 )) ” 
  &&  “ (numc = need_pre) ” 
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
  &&  “ (0 <= numc) ” 
  &&  “ (numc <= i) ” 
  &&  “ (0 <= ch) ” 
  &&  “ (ch <= 127) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l i start numc need_pre output_rows ) ”
  &&  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Definition select_words_partial_solve_wit_10 := select_words_partial_solve_wit_10_pure -> select_words_partial_solve_wit_10_aux.

Definition select_words_partial_solve_wit_11 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k < len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= addc)) (PreH9 : (addc <= 1)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH29 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
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
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len) ”
  &&  (((w + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w k k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
.

Definition select_words_partial_solve_wit_12 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (k >= len)) (PreH2 : (n = (string_length (str_l)))) (PreH3 : (out <> 0)) (PreH4 : (data <> 0)) (PreH5 : (w <> 0)) (PreH6 : (0 <= ch)) (PreH7 : (ch <= 127)) (PreH8 : (0 <= addc)) (PreH9 : (addc <= 1)) (PreH10 : (0 <= out_size)) (PreH11 : (out_size <= n)) (PreH12 : (out_size = (Zlength (output_rows)))) (PreH13 : ((Zlength (output_ptrs)) = out_size)) (PreH14 : (0 <= start)) (PreH15 : (start < n)) (PreH16 : (len = (n - start ))) (PreH17 : (numc = need_pre)) (PreH18 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH19 : (0 <= k)) (PreH20 : (k <= len)) (PreH21 : (0 <= need_pre)) (PreH22 : (need_pre < INT_MAX)) (PreH23 : (valid_string str_l )) (PreH24 : (all_ascii str_l )) (PreH25 : (valid_select_words_input_117 str_l )) (PreH26 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH27 : (problem_117_pre_z str_l )) (PreH28 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH29 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH30 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (store_string s_pre str_l )
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
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
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len) ”
  &&  (((w + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  (CharArray.undef_missing_i w len k (len + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
  **  (CharArray.full w k (word_payload_117 (str_l) (start) ((start + k ))) )
.

Definition select_words_partial_solve_wit_13 := 
forall (need_pre: Z) (s_pre: Z) (str_l: (@list Z)) (k: Z) (numc: Z) (len: Z) (start: Z) (output_ptrs: (@list Z)) (output_rows: (@list (@list Z))) (out_size: Z) (addc: Z) (ch: Z) (w: Z) (data: Z) (out: Z) (n: Z) (PreH1 : (0 <= ((string_length (str_l)) + 1 ))) (PreH2 : (k >= len)) (PreH3 : (n = (string_length (str_l)))) (PreH4 : (out <> 0)) (PreH5 : (data <> 0)) (PreH6 : (w <> 0)) (PreH7 : (0 <= ch)) (PreH8 : (ch <= 127)) (PreH9 : (0 <= addc)) (PreH10 : (addc <= 1)) (PreH11 : (0 <= out_size)) (PreH12 : (out_size <= n)) (PreH13 : (out_size = (Zlength (output_rows)))) (PreH14 : ((Zlength (output_ptrs)) = out_size)) (PreH15 : (0 <= start)) (PreH16 : (start < n)) (PreH17 : (len = (n - start ))) (PreH18 : (numc = need_pre)) (PreH19 : (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n)))))) (PreH20 : (0 <= k)) (PreH21 : (k <= len)) (PreH22 : (0 <= need_pre)) (PreH23 : (need_pre < INT_MAX)) (PreH24 : (valid_string str_l )) (PreH25 : (all_ascii str_l )) (PreH26 : (valid_select_words_input_117 str_l )) (PreH27 : (((string_length (str_l)) + 2 ) < INT_MAX)) (PreH28 : (problem_117_pre_z str_l )) (PreH29 : (select_scan_state_117 str_l n start numc need_pre output_rows )) (PreH30 : ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n)))) (PreH31 : ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len)) ,
  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.undef_seg w (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (PtrArray.undef_seg data out_size (n + 1 ) )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
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
  &&  “ (0 <= addc) ” 
  &&  “ (addc <= 1) ” 
  &&  “ (0 <= out_size) ” 
  &&  “ (out_size <= n) ” 
  &&  “ (out_size = (Zlength (output_rows))) ” 
  &&  “ ((Zlength (output_ptrs)) = out_size) ” 
  &&  “ (0 <= start) ” 
  &&  “ (start < n) ” 
  &&  “ (len = (n - start )) ” 
  &&  “ (numc = need_pre) ” 
  &&  “ (numc = (count_consonants_z_117 ((word_payload_117 (str_l) (start) (n))))) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= len) ” 
  &&  “ (0 <= need_pre) ” 
  &&  “ (need_pre < INT_MAX) ” 
  &&  “ (valid_string str_l ) ” 
  &&  “ (all_ascii str_l ) ” 
  &&  “ (valid_select_words_input_117 str_l ) ” 
  &&  “ (((string_length (str_l)) + 2 ) < INT_MAX) ” 
  &&  “ (problem_117_pre_z str_l ) ” 
  &&  “ (select_scan_state_117 str_l n start numc need_pre output_rows ) ” 
  &&  “ ((select_current_117 (str_l) (n) (need_pre)) = (word_payload_117 (str_l) (start) (n))) ” 
  &&  “ ((Zlength ((word_payload_117 (str_l) (start) (n)))) = len) ”
  &&  (((data + (out_size * sizeof(PTR) ) )) # Ptr  |->_)
  **  (PtrArray.undef_seg data (out_size + 1 ) (n + 1 ) )
  **  (CharArray.full w (k + 1 ) (app ((word_payload_117 (str_l) (start) ((start + k )))) ((cons (0) ((@nil Z))))) )
  **  (CharArray.full s_pre ((string_length (str_l)) + 1 ) (c_string (str_l)) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> out_size)
  **  (PtrArray.seg data 0 out_size output_ptrs )
  **  (select_words_rows_heap_117 output_ptrs output_rows )
.

Module Type VC_Correct.

Include ptr_array2_Strategy_Correct.
Include char_array_Strategy_Correct.
Include string_Strategy_Correct.

Axiom proof_of_is_consonant_char_safety_wit_1 : is_consonant_char_safety_wit_1.
Axiom proof_of_is_consonant_char_safety_wit_2 : is_consonant_char_safety_wit_2.
Axiom proof_of_is_consonant_char_safety_wit_3 : is_consonant_char_safety_wit_3.
Axiom proof_of_is_consonant_char_safety_wit_4 : is_consonant_char_safety_wit_4.
Axiom proof_of_is_consonant_char_safety_wit_5 : is_consonant_char_safety_wit_5.
Axiom proof_of_is_consonant_char_safety_wit_6 : is_consonant_char_safety_wit_6.
Axiom proof_of_is_consonant_char_safety_wit_7 : is_consonant_char_safety_wit_7.
Axiom proof_of_is_consonant_char_safety_wit_8 : is_consonant_char_safety_wit_8.
Axiom proof_of_is_consonant_char_safety_wit_9 : is_consonant_char_safety_wit_9.
Axiom proof_of_is_consonant_char_safety_wit_10 : is_consonant_char_safety_wit_10.
Axiom proof_of_is_consonant_char_safety_wit_11 : is_consonant_char_safety_wit_11.
Axiom proof_of_is_consonant_char_safety_wit_12 : is_consonant_char_safety_wit_12.
Axiom proof_of_is_consonant_char_safety_wit_13 : is_consonant_char_safety_wit_13.
Axiom proof_of_is_consonant_char_safety_wit_14 : is_consonant_char_safety_wit_14.
Axiom proof_of_is_consonant_char_safety_wit_15 : is_consonant_char_safety_wit_15.
Axiom proof_of_is_consonant_char_safety_wit_16 : is_consonant_char_safety_wit_16.
Axiom proof_of_is_consonant_char_safety_wit_17 : is_consonant_char_safety_wit_17.
Axiom proof_of_is_consonant_char_safety_wit_18 : is_consonant_char_safety_wit_18.
Axiom proof_of_is_consonant_char_safety_wit_19 : is_consonant_char_safety_wit_19.
Axiom proof_of_is_consonant_char_safety_wit_20 : is_consonant_char_safety_wit_20.
Axiom proof_of_is_consonant_char_safety_wit_21 : is_consonant_char_safety_wit_21.
Axiom proof_of_is_consonant_char_safety_wit_22 : is_consonant_char_safety_wit_22.
Axiom proof_of_is_consonant_char_safety_wit_23 : is_consonant_char_safety_wit_23.
Axiom proof_of_is_consonant_char_safety_wit_24 : is_consonant_char_safety_wit_24.
Axiom proof_of_is_consonant_char_safety_wit_25 : is_consonant_char_safety_wit_25.
Axiom proof_of_is_consonant_char_safety_wit_26 : is_consonant_char_safety_wit_26.
Axiom proof_of_is_consonant_char_safety_wit_27 : is_consonant_char_safety_wit_27.
Axiom proof_of_is_consonant_char_safety_wit_28 : is_consonant_char_safety_wit_28.
Axiom proof_of_is_consonant_char_safety_wit_29 : is_consonant_char_safety_wit_29.
Axiom proof_of_is_consonant_char_safety_wit_30 : is_consonant_char_safety_wit_30.
Axiom proof_of_is_consonant_char_safety_wit_31 : is_consonant_char_safety_wit_31.
Axiom proof_of_is_consonant_char_safety_wit_32 : is_consonant_char_safety_wit_32.
Axiom proof_of_is_consonant_char_safety_wit_33 : is_consonant_char_safety_wit_33.
Axiom proof_of_is_consonant_char_safety_wit_34 : is_consonant_char_safety_wit_34.
Axiom proof_of_is_consonant_char_safety_wit_35 : is_consonant_char_safety_wit_35.
Axiom proof_of_is_consonant_char_safety_wit_36 : is_consonant_char_safety_wit_36.
Axiom proof_of_is_consonant_char_safety_wit_37 : is_consonant_char_safety_wit_37.
Axiom proof_of_is_consonant_char_safety_wit_38 : is_consonant_char_safety_wit_38.
Axiom proof_of_is_consonant_char_safety_wit_39 : is_consonant_char_safety_wit_39.
Axiom proof_of_is_consonant_char_safety_wit_40 : is_consonant_char_safety_wit_40.
Axiom proof_of_is_consonant_char_safety_wit_41 : is_consonant_char_safety_wit_41.
Axiom proof_of_is_consonant_char_safety_wit_42 : is_consonant_char_safety_wit_42.
Axiom proof_of_is_consonant_char_safety_wit_43 : is_consonant_char_safety_wit_43.
Axiom proof_of_is_consonant_char_safety_wit_44 : is_consonant_char_safety_wit_44.
Axiom proof_of_is_consonant_char_safety_wit_45 : is_consonant_char_safety_wit_45.
Axiom proof_of_is_consonant_char_safety_wit_46 : is_consonant_char_safety_wit_46.
Axiom proof_of_is_consonant_char_safety_wit_47 : is_consonant_char_safety_wit_47.
Axiom proof_of_is_consonant_char_safety_wit_48 : is_consonant_char_safety_wit_48.
Axiom proof_of_is_consonant_char_safety_wit_49 : is_consonant_char_safety_wit_49.
Axiom proof_of_is_consonant_char_safety_wit_50 : is_consonant_char_safety_wit_50.
Axiom proof_of_is_consonant_char_safety_wit_51 : is_consonant_char_safety_wit_51.
Axiom proof_of_is_consonant_char_return_wit_1 : is_consonant_char_return_wit_1.
Axiom proof_of_is_consonant_char_return_wit_2 : is_consonant_char_return_wit_2.
Axiom proof_of_is_consonant_char_return_wit_3 : is_consonant_char_return_wit_3.
Axiom proof_of_is_consonant_char_return_wit_4 : is_consonant_char_return_wit_4.
Axiom proof_of_is_consonant_char_return_wit_5 : is_consonant_char_return_wit_5.
Axiom proof_of_is_consonant_char_return_wit_6 : is_consonant_char_return_wit_6.
Axiom proof_of_is_consonant_char_return_wit_7 : is_consonant_char_return_wit_7.
Axiom proof_of_is_consonant_char_return_wit_8 : is_consonant_char_return_wit_8.
Axiom proof_of_is_consonant_char_return_wit_9 : is_consonant_char_return_wit_9.
Axiom proof_of_is_consonant_char_return_wit_10 : is_consonant_char_return_wit_10.
Axiom proof_of_is_consonant_char_return_wit_11 : is_consonant_char_return_wit_11.
Axiom proof_of_is_consonant_char_return_wit_12 : is_consonant_char_return_wit_12.
Axiom proof_of_is_consonant_char_return_wit_13 : is_consonant_char_return_wit_13.
Axiom proof_of_is_consonant_char_return_wit_14 : is_consonant_char_return_wit_14.
Axiom proof_of_is_consonant_char_return_wit_15 : is_consonant_char_return_wit_15.
Axiom proof_of_select_words_safety_wit_1 : select_words_safety_wit_1.
Axiom proof_of_select_words_safety_wit_2 : select_words_safety_wit_2.
Axiom proof_of_select_words_safety_wit_3 : select_words_safety_wit_3.
Axiom proof_of_select_words_safety_wit_4 : select_words_safety_wit_4.
Axiom proof_of_select_words_safety_wit_5 : select_words_safety_wit_5.
Axiom proof_of_select_words_safety_wit_6 : select_words_safety_wit_6.
Axiom proof_of_select_words_safety_wit_7 : select_words_safety_wit_7.
Axiom proof_of_select_words_safety_wit_8 : select_words_safety_wit_8.
Axiom proof_of_select_words_safety_wit_9 : select_words_safety_wit_9.
Axiom proof_of_select_words_safety_wit_10 : select_words_safety_wit_10.
Axiom proof_of_select_words_safety_wit_11 : select_words_safety_wit_11.
Axiom proof_of_select_words_safety_wit_12 : select_words_safety_wit_12.
Axiom proof_of_select_words_safety_wit_13 : select_words_safety_wit_13.
Axiom proof_of_select_words_safety_wit_14 : select_words_safety_wit_14.
Axiom proof_of_select_words_safety_wit_15 : select_words_safety_wit_15.
Axiom proof_of_select_words_safety_wit_16 : select_words_safety_wit_16.
Axiom proof_of_select_words_safety_wit_17 : select_words_safety_wit_17.
Axiom proof_of_select_words_safety_wit_18 : select_words_safety_wit_18.
Axiom proof_of_select_words_safety_wit_19 : select_words_safety_wit_19.
Axiom proof_of_select_words_safety_wit_20 : select_words_safety_wit_20.
Axiom proof_of_select_words_safety_wit_21 : select_words_safety_wit_21.
Axiom proof_of_select_words_safety_wit_22 : select_words_safety_wit_22.
Axiom proof_of_select_words_safety_wit_23 : select_words_safety_wit_23.
Axiom proof_of_select_words_safety_wit_24 : select_words_safety_wit_24.
Axiom proof_of_select_words_safety_wit_25 : select_words_safety_wit_25.
Axiom proof_of_select_words_safety_wit_26 : select_words_safety_wit_26.
Axiom proof_of_select_words_safety_wit_27 : select_words_safety_wit_27.
Axiom proof_of_select_words_safety_wit_28 : select_words_safety_wit_28.
Axiom proof_of_select_words_safety_wit_29 : select_words_safety_wit_29.
Axiom proof_of_select_words_safety_wit_30 : select_words_safety_wit_30.
Axiom proof_of_select_words_safety_wit_31 : select_words_safety_wit_31.
Axiom proof_of_select_words_safety_wit_32 : select_words_safety_wit_32.
Axiom proof_of_select_words_safety_wit_33 : select_words_safety_wit_33.
Axiom proof_of_select_words_safety_wit_34 : select_words_safety_wit_34.
Axiom proof_of_select_words_safety_wit_35 : select_words_safety_wit_35.
Axiom proof_of_select_words_safety_wit_36 : select_words_safety_wit_36.
Axiom proof_of_select_words_safety_wit_37 : select_words_safety_wit_37.
Axiom proof_of_select_words_safety_wit_38 : select_words_safety_wit_38.
Axiom proof_of_select_words_safety_wit_39 : select_words_safety_wit_39.
Axiom proof_of_select_words_safety_wit_40 : select_words_safety_wit_40.
Axiom proof_of_select_words_safety_wit_41 : select_words_safety_wit_41.
Axiom proof_of_select_words_safety_wit_42 : select_words_safety_wit_42.
Axiom proof_of_select_words_safety_wit_43 : select_words_safety_wit_43.
Axiom proof_of_select_words_safety_wit_44 : select_words_safety_wit_44.
Axiom proof_of_select_words_safety_wit_45 : select_words_safety_wit_45.
Axiom proof_of_select_words_safety_wit_46 : select_words_safety_wit_46.
Axiom proof_of_select_words_safety_wit_47 : select_words_safety_wit_47.
Axiom proof_of_select_words_safety_wit_48 : select_words_safety_wit_48.
Axiom proof_of_select_words_safety_wit_49 : select_words_safety_wit_49.
Axiom proof_of_select_words_safety_wit_50 : select_words_safety_wit_50.
Axiom proof_of_select_words_safety_wit_51 : select_words_safety_wit_51.
Axiom proof_of_select_words_safety_wit_52 : select_words_safety_wit_52.
Axiom proof_of_select_words_safety_wit_53 : select_words_safety_wit_53.
Axiom proof_of_select_words_safety_wit_54 : select_words_safety_wit_54.
Axiom proof_of_select_words_safety_wit_55 : select_words_safety_wit_55.
Axiom proof_of_select_words_safety_wit_56 : select_words_safety_wit_56.
Axiom proof_of_select_words_safety_wit_57 : select_words_safety_wit_57.
Axiom proof_of_select_words_safety_wit_58 : select_words_safety_wit_58.
Axiom proof_of_select_words_safety_wit_59 : select_words_safety_wit_59.
Axiom proof_of_select_words_safety_wit_60 : select_words_safety_wit_60.
Axiom proof_of_select_words_safety_wit_61 : select_words_safety_wit_61.
Axiom proof_of_select_words_safety_wit_62 : select_words_safety_wit_62.
Axiom proof_of_select_words_entail_wit_1 : select_words_entail_wit_1.
Axiom proof_of_select_words_entail_wit_2 : select_words_entail_wit_2.
Axiom proof_of_select_words_entail_wit_3 : select_words_entail_wit_3.
Axiom proof_of_select_words_entail_wit_4 : select_words_entail_wit_4.
Axiom proof_of_select_words_entail_wit_5 : select_words_entail_wit_5.
Axiom proof_of_select_words_entail_wit_6 : select_words_entail_wit_6.
Axiom proof_of_select_words_entail_wit_7 : select_words_entail_wit_7.
Axiom proof_of_select_words_entail_wit_8_1 : select_words_entail_wit_8_1.
Axiom proof_of_select_words_entail_wit_8_2 : select_words_entail_wit_8_2.
Axiom proof_of_select_words_entail_wit_8_3 : select_words_entail_wit_8_3.
Axiom proof_of_select_words_entail_wit_8_4 : select_words_entail_wit_8_4.
Axiom proof_of_select_words_entail_wit_9_1 : select_words_entail_wit_9_1.
Axiom proof_of_select_words_entail_wit_9_2 : select_words_entail_wit_9_2.
Axiom proof_of_select_words_entail_wit_9_3 : select_words_entail_wit_9_3.
Axiom proof_of_select_words_entail_wit_9_4 : select_words_entail_wit_9_4.
Axiom proof_of_select_words_entail_wit_10 : select_words_entail_wit_10.
Axiom proof_of_select_words_entail_wit_11 : select_words_entail_wit_11.
Axiom proof_of_select_words_entail_wit_12_1 : select_words_entail_wit_12_1.
Axiom proof_of_select_words_entail_wit_12_2 : select_words_entail_wit_12_2.
Axiom proof_of_select_words_entail_wit_12_3 : select_words_entail_wit_12_3.
Axiom proof_of_select_words_return_wit_1 : select_words_return_wit_1.
Axiom proof_of_select_words_partial_solve_wit_1_pure : select_words_partial_solve_wit_1_pure.
Axiom proof_of_select_words_partial_solve_wit_1 : select_words_partial_solve_wit_1.
Axiom proof_of_select_words_partial_solve_wit_2 : select_words_partial_solve_wit_2.
Axiom proof_of_select_words_partial_solve_wit_3_pure : select_words_partial_solve_wit_3_pure.
Axiom proof_of_select_words_partial_solve_wit_3 : select_words_partial_solve_wit_3.
Axiom proof_of_select_words_partial_solve_wit_4_pure : select_words_partial_solve_wit_4_pure.
Axiom proof_of_select_words_partial_solve_wit_4 : select_words_partial_solve_wit_4.
Axiom proof_of_select_words_partial_solve_wit_5 : select_words_partial_solve_wit_5.
Axiom proof_of_select_words_partial_solve_wit_6 : select_words_partial_solve_wit_6.
Axiom proof_of_select_words_partial_solve_wit_7 : select_words_partial_solve_wit_7.
Axiom proof_of_select_words_partial_solve_wit_8_pure : select_words_partial_solve_wit_8_pure.
Axiom proof_of_select_words_partial_solve_wit_8 : select_words_partial_solve_wit_8.
Axiom proof_of_select_words_partial_solve_wit_9_pure : select_words_partial_solve_wit_9_pure.
Axiom proof_of_select_words_partial_solve_wit_9 : select_words_partial_solve_wit_9.
Axiom proof_of_select_words_partial_solve_wit_10_pure : select_words_partial_solve_wit_10_pure.
Axiom proof_of_select_words_partial_solve_wit_10 : select_words_partial_solve_wit_10.
Axiom proof_of_select_words_partial_solve_wit_11 : select_words_partial_solve_wit_11.
Axiom proof_of_select_words_partial_solve_wit_12 : select_words_partial_solve_wit_12.
Axiom proof_of_select_words_partial_solve_wit_13 : select_words_partial_solve_wit_13.

End VC_Correct.
